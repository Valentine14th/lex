from abc import ABC, abstractmethod
from decimal import Decimal
from queue import Queue, PriorityQueue
from subprocess import Popen, PIPE, STDOUT
from threading import Thread, Event
from time import time, sleep
import datetime
import re
import json
import os
import shutil
from typing import Any, List, Dict, Set, Tuple, Union

from instrlib.timer import Timer
from instrlib.pep import PEP
from instrlib.handler_graph import max_element
from instrlib.event import TimedTuple

class PDP(ABC):

    def __init__(self, name : str = "enforcer", log_file : Union[str, None] = None, timer_state_file : Union[str, None] = None):
        self.name             : str            = name
        self.log_file         : str     | None = log_file
        self.ocaml_proc       : Popen   | None = None
        self.timer_thread     : Thread  | None = None
        self.writer_thread    : Thread  | None = None
        self.reader_thread    : Thread  | None = None
        self.pep              : PEP     | None = None
        self.write_prio       : PriorityQueue  = PriorityQueue()
        self.timer            : Timer          = Timer(state_file=timer_state_file)
        self.termination_flag : Event          = Event()
        self.read_queue       : Queue          = Queue()
        self.cpu_core         : int     | None = None
        self.timer_state_file : str | None     = timer_state_file
        
    @abstractmethod
    def ts_bytes(self, stm : str, tsp : Union[float, None] = None, flag_q : bool = False) -> bytes:
        pass

    @abstractmethod
    def command(self) -> List[str]:
        pass 

    @abstractmethod
    def parse_events(self, input_string : str) -> Dict[str, Set[Tuple[str, ...]]]:
        pass

    @abstractmethod
    def tick(self) -> str:
        pass

    def run_timer_thread(self) -> None:
        timer(self, self.write_prio, 1)

    def run_writer_thread(self) -> None:
        if self.ocaml_proc is not None:
            writer(self, self.log_file)
        else:
            _print("writer", self.name, "Failed to start writer thread: no process specified")

    def run_reader_thread(self) -> None:
        if self.ocaml_proc is not None and self.pep is not None:
            reader(self)
        else:
            _print("reader", self.name, "Failed to start reader thread: no process or no cau_graph specified")

    """
    start all threads and the enforcer
    """
    def start_threads(self) -> None:
        cmd = self.command()

        preexec_fn = None
        if self.cpu_core is not None and hasattr(os, "sched_setaffinity"):
            cpu_core = self.cpu_core

            def _pin_to_cpu() -> None:
                os.sched_setaffinity(0, {cpu_core})

            preexec_fn = _pin_to_cpu

        print(' '.join(cmd))
        self.ocaml_proc    = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT, preexec_fn=preexec_fn)

        self.timer_thread  = Thread(target=self.run_timer_thread)
        self.writer_thread = Thread(target=self.run_writer_thread)
        self.reader_thread = Thread(target=self.run_reader_thread)

        self.timer_thread.start()
        self.writer_thread.start()
        self.reader_thread.start()
    

class EnfGuard(PDP):

    def __init__(self, exe : str, sig : str, formula : str, *args, **kwargs):
        cpu_core = kwargs.pop('cpu_core', None)
        self.func : str | None = kwargs.pop('func', None)
        self.state_file : str | None = kwargs.pop('state_file', None)
        super(EnfGuard, self).__init__(*args, timer_state_file=self.state_file, **kwargs)
        self.exe     : str = exe
        self.sig     : str = sig
        self.formula : str = formula
        self.allowed_events : Set[str] = self._parse_signature_file(sig)
        self.cpu_core : int | None = int(cpu_core) if cpu_core is not None else None
        if self.cpu_core is None:
            env_cpu = os.getenv("INSTRLIB_PIN_CPU")
            if env_cpu is not None and env_cpu.strip() != "":
                try:
                    self.cpu_core = int(env_cpu.strip())
                except ValueError:
                    print(f"[EnfGuard] Warning: invalid INSTRLIB_PIN_CPU='{env_cpu}', ignoring")
    
    def _parse_signature_file(self, sig_path : str) -> Set[str]:
        """
        Parse the signature file and extract event names.
        Returns a set of event names that this enforcer understands.
        """
        allowed_events = set()
        try:
            with open(sig_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    # Skip empty lines, comments, and function declarations
                    if not line or line.startswith('//') or line.startswith('fun '):
                        continue
                    # Extract event name (everything before the opening parenthesis)
                    if '(' in line:
                        event_name = line.split('(')[0].strip()
                        allowed_events.add(event_name)
            if not allowed_events:
                raise RuntimeError(
                    f"[EnfGuard] Signature file parsed but contains no event declarations: {sig_path}"
                )
            print(f"[EnfGuard] Parsed signature {sig_path}: {len(allowed_events)} events")
        except FileNotFoundError:
            raise RuntimeError(f"[EnfGuard] Signature file not found: {sig_path}")
        except Exception as e:
            raise RuntimeError(f"[EnfGuard] Error parsing signature {sig_path}: {e}") from e
        return allowed_events
    
    def accepts_event(self, event_name : str) -> bool:
        """Check if this enforcer accepts the given event name"""
        return event_name in self.allowed_events

    def ts_bytes(self, stm : str, tsp : Union[float, None] = None, flag_q : bool = False) -> bytes:
        tsp = tsp if tsp is not None else time() * 1000
        tsp2 = str(int(tsp))
        if stm == '':
            return b'@' + tsp2.encode() + b';\n'
        elif flag_q:
            return b'@' + tsp2.encode() + b' ' + stm.encode() + b'?\n'
        else:
            return b'@' + tsp2.encode() + b' ' + str(stm).encode() + b';\n'
    
    def command(self):
        command = [
            self.exe,
            '-sig',     self.sig,
            '-formula', self.formula,
            '-json',
        ]
        if self.func is not None:
            command += ['-func', self.func]
        if self.state_file is not None:
            command += ['-state', self.state_file]
        return command
    
    def parse_events(self, input_string : str) -> Dict[str, Set[Tuple[str, ...]]]:
        event_pattern = r'(\w+)\(((?:[^()"]|"(?:[^"\\]|\\.)*")*)\)' #r'(\w+)\((.*?)\)'
        matches = re.findall(event_pattern, input_string)
        event_args: Dict[str, Set[Tuple[str, ...]]] = {}
        for event_name, args in matches:
            arg_tuple = tuple(arg.strip() for arg in args.split(','))
            if event_name in event_args:
                event_args[event_name].add(arg_tuple)
            else:
                event_args[event_name] = {arg_tuple}
        return event_args
        
    def tick(self) -> str:
        return "tick()"
    
NO_PRINT = False

def _print(agent : str, name : str, msg : str) -> None:
    if NO_PRINT: return
    colors = {
        "black": "\033[30m",
        "red": "\033[31m",
        "green": "\033[32m",
        "yellow": "\033[33m",
        "blue": "\033[34m",
        "magenta": "\033[35m",
        "cyan": "\033[36m",
        "white": "\033[37m",
        "reset": "\033[0m",
    }
    color = {
        "writer":    "green",
        "reader":    "yellow",
        "timer" :    "blue",
        "proactive": "magenta",
    }.get(agent, "black")
    current_time = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")
    agent_with_name = f"{agent}[{name}]"
    agent_formatted = agent_with_name + (10 - len(agent_with_name)) * ' '
    formatted_msg = f"[{current_time}] [{agent_formatted}]: {msg}"
    color_code = colors.get(color.lower(), colors["reset"])
    print(f"{color_code}{formatted_msg}{colors['reset']}", flush=True)


"""
writer thread reads events from write_prio and writes statements to enforcer and read_queue
additionally, latency statements are sent to whyenf 
"""
def writer(enforcer : PDP, log_file : Union[str, None]) -> None:
    _print("writer", enforcer.name, "Starting")
    while True:
        stm = b''
        event : TimedTuple = enforcer.write_prio.get()
        tsp = event.tsp
        (flag, innerqueue, stm) = event.event_tuple
        if event.expects_response:
            enforcer.read_queue.put(TimedTuple(tsp, (flag, innerqueue, stm), batch_id=event.batch_id))
        assert enforcer.ocaml_proc is not None
        if enforcer.ocaml_proc.poll() is None:
            try:
                if log_file is not None:
                    with open(log_file, 'a') as log:
                        log.write(stm.decode() + "\n")
                assert enforcer.ocaml_proc.stdin is not None
                enforcer.ocaml_proc.stdin.write(stm)
                enforcer.ocaml_proc.stdin.flush()
                _print("writer", enforcer.name, f"Sent to enforcer: {stm.decode()}")
            except Exception as e:
                _print("writer", enforcer.name, f"Error: {e}")
    _print("writer", enforcer.name, "Terminated")


"""
reader thread matches response of enforcer with statements from read_queue;
used to create a proactive thread or wake up worker thread
"""            
def reader(enforcer : PDP) -> None:
    _print("reader", enforcer.name, "Starting")

    def getstm(proc):
        output = proc.stdout.readline()
        while output:
            msg = output.decode()
            try:
                return json.loads(msg)            
            except:
                _print("reader", enforcer.name, f"Skipping non-JSON: {msg[:-1]}")
            output = proc.stdout.readline()
        return None

    assert enforcer.ocaml_proc is not None
    while enforcer.ocaml_proc.poll() is None: 
        try:
            assert enforcer.ocaml_proc.stdout is not None
            msg = getstm(enforcer.ocaml_proc)
            if msg is not None:
                event = enforcer.read_queue.get()
                bid = f" batch_id={event.batch_id}" if event.batch_id is not None else ""
                _print("reader", enforcer.name, f"Received from enforcer:{bid} {msg}")
                (flag, innerqueue, order_msg) = event.event_tuple
                _print("reader", enforcer.name, f"Matching request:{bid} {order_msg.decode()}")
                small_queue : Queue = Queue()
                small_queue.put(msg)
                innerqueue.put(small_queue)
                if msg.get("proactive", False) and len(msg.get("cause", [])) > 0:
                    handle_proactive_commands(msg, enforcer)
                flag.set()
        except Exception as e:
            _print("reader", enforcer.name, f"Error: {e}")
    assert enforcer.ocaml_proc.stdout is not None
    enforcer.ocaml_proc.stdout.close()

    _print("reader", enforcer.name, "Terminated")


"""
timer thread providing timestamps to enforcer
"""
def timer(enforcer : PDP, order : PriorityQueue, unit : float = 1):
    _print("timer", enforcer.name, "Starting")
    timer = enforcer.timer
    while True:
        with timer.current_time_lock:
            if not timer.first_time:
                timer.current_time += 1
            tsp = timer.current_time
            stm = enforcer.ts_bytes(enforcer.tick(), tsp)
            event = Event()
            _print("timer", enforcer.name, f"tick({tsp})")
            order.put(TimedTuple(tsp, (event, Queue(), stm), expects_response = not timer.first_time))
            timer.first_time = False
        sleep(unit)
    _print("timer", enforcer.name, "Terminated")


"""Handle proactive commands by spawning a new thread and measure its performance"""
def handle_proactive_commands(msg : str, enforcer : PDP):
    start = time()
    proac_thread = Thread(target=spawn_proactive_thread, args=(msg, enforcer))
    proac_thread.start()
    proac_thread.join()
    end = time()
    _print("proactive", enforcer.name, f'Terminated. Time thread spawned: {end - start}, current time {time()}')


"""
newly spawned proactive worker thread used to proactively cause events
"""
def spawn_proactive_thread(msg : Dict[str, Any], enforcer : PDP) -> None:
    _print("proactive", enforcer.name, f"Starting newly spawned proactive thread: {msg}")
    for event_json in msg["cause"]:
        name = event_json['name']
        args = event_json['args']
        for arg in args:
            _print("proactive", enforcer.name, f'Event to be proactively caused: {name} with arguments {arg}')
    event_names = tuple({event_json['name'] for event_json in msg['cause']})
    assert enforcer.pep is not None
    max = max_element(enforcer.pep.cau_graph, event_names)
    _print("proactive", enforcer.name, f'Max element: {max}')
    for h_key in max:
        handler = enforcer.pep.cau_event_map.get(h_key)
        if handler is None:
            _print("proactive", enforcer.name, f"Failed to find a handler for {h_key}")
        else:
            handler([event_json for event_json in msg["cause"] if event_json['name'] in h_key])


class MultiPDP:
    """
    Manages multiple PDP instances for parallel enforcement of multiple formulas.
    Broadcasts events to all enforcers and aggregates their responses.
    """
    
    def __init__(self, log_file : Union[str, None] = None):
        self.enforcers : List[Tuple[str, PDP]] = []  # List of (name, pdp) tuples
        self.log_file = log_file
        self.pep : PEP | None = None
        self.pinned_cpus : List[int] = self._discover_pinned_cpus()

    def _discover_pinned_cpus(self) -> List[int]:
        raw = os.getenv("INSTRLIB_PIN_CPUS", "")
        if raw.strip() != "":
            try:
                return [int(cpu.strip()) for cpu in raw.split(',') if cpu.strip() != ""]
            except ValueError:
                print(f"[MultiPDP] Warning: invalid INSTRLIB_PIN_CPUS='{raw}', ignoring")

        if hasattr(os, "sched_getaffinity"):
            return sorted(os.sched_getaffinity(0))

        cpu_count = os.cpu_count()
        if cpu_count is None:
            return []
        return list(range(cpu_count))
        
    def add_enforcer(self, name : str, exe : str, sig : str, formula : str, func : Union[str, None] = None, state_file : Union[str, None] = None) -> None:
        """Add a new enforcer with the given name and configuration"""
        cpu_core : int | None = None
        if self.pinned_cpus:
            cpu_core = self.pinned_cpus[len(self.enforcers) % len(self.pinned_cpus)]

        pdp = EnfGuard(
            name=name,
            exe=exe,
            sig=sig,
            formula=formula,
            log_file=self.log_file,
            cpu_core=cpu_core,
            func=func,
            state_file=state_file,
        )
        self.enforcers.append((name, pdp))
        if cpu_core is None:
            print(f"[MultiPDP] Added enforcer '{name}' for formula: {formula}")
        else:
            print(f"[MultiPDP] Added enforcer '{name}' for formula: {formula} (cpu={cpu_core})")
    
    def start_threads(self) -> None:
        """Start all enforcers in parallel"""
        if not self.enforcers:
            raise Exception("No enforcers added to MultiPDP")
        
        print(f"[MultiPDP] Starting {len(self.enforcers)} enforcer(s)...")
        for name, pdp in self.enforcers:
            # Set the pep for each enforcer
            if self.pep is not None:
                pdp.pep = self.pep
            # Start threads for this enforcer
            pdp.start_threads()
        print(f"[MultiPDP] All enforcers started successfully")
    
    def get_enforcer(self, name : str) -> Union[PDP, None]:
        """Get an enforcer by name"""
        for enf_name, pdp in self.enforcers:
            if enf_name == name:
                return pdp
        return None
    
    def get_all_enforcers(self) -> List[Tuple[str, PDP]]:
        """Get all enforcers as (name, pdp) tuples"""
        return self.enforcers