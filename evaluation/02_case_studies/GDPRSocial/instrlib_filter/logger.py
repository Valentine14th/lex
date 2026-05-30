from abc import ABC, abstractmethod
import os
from queue import Queue
from random import random
import threading
from time import time, perf_counter
from typing import Tuple, List, Set, Union, Dict, Any

from instrlib.pdp import PDP, _print
from instrlib.event import *
from instrlib.pep import PEP
from instrlib.schema import Schema


class TimedCompletionEvent(threading.Event):
    """Event that records the perf_counter timestamp at completion."""

    def __init__(self):
        super().__init__()
        self.done_perf: float | None = None

    def set(self):
        self.done_perf = perf_counter()
        super().set()


class BaseLogger(ABC):
    """
    Abstract base class for Logger and MultiLogger with shared functionality.
    """
    
    def __init__(self, pep : PEP, schema : Schema, cache_timeout : int = 10):
        self.pep = pep
        self.schema = schema
        self.cache_timeout = cache_timeout
        
        # Validate schema against PEP mapping
        for _, event in self.pep.mapping.items():            
            if event.name not in schema.mapping:
                Exception(f"Event {event} is not defined in the schema.")
        
        # Aggregated state (used by both Logger and MultiLogger)
        self.sup_events : Set[str] = set()
        self.cau_events : Set[str] = set()
        self.sup_enc : Dict[str, List[Tuple[Any, ...]]] = {}
        self.cau_enc : Dict[str, List[Tuple[Any, ...]]] = {}
    
    def _reset(self):
        """Reset aggregated state - can be overridden by subclasses"""
        self.sup_events = set()
        self.cau_events = set()
        self.sup_enc = {}
        self.cau_enc = {}
    
    def extend_mapping(self, pep : PEP) -> None:
        """Extend the PEP mapping - must be overridden if needed"""
        self.pep = self.pep | pep
    
    def extend_schema(self, schema : Schema) -> None:
        """Extend the schema"""
        self.schema = self.schema | schema
    
    def make_cache_key(self, events: List[Event]) -> Tuple[Event, ...]:
        """Create cache key from events list"""
        return tuple(events)
    
    def parse_args(self, name : str, args : Tuple[str, ...]) -> Tuple[Any, ...]:
        """Parse and type-check event arguments against schema"""
        if name not in self.schema: 
            raise Exception(f'the event {name} is not defined in the schema')
        schema_types = self.schema.get_types(name)
        new_args : List[Any] = []
        for arg_idx, (arg, arg_type) in enumerate(zip(args, schema_types)):
            if arg_type is str:
                new_args.append(arg)
            elif arg_type is float and arg.isnumeric():
                new_args.append(float(arg))
            elif arg_type is int and arg.isnumeric():
                new_args.append(int(arg))
            else:
                raise Exception(f'Type mismatch for event {name}. Expected {arg_type} for arg {arg_idx}, got {type(arg)}.')
        return tuple(new_args)
    
    def check_type(self, events : List[Event]):
        """Validate events against schema and perform type conversion"""
        for idx, event in enumerate(events):
            if event.name not in self.schema: 
                raise Exception(f'The event {event.name} is not defined in the schema')
            num_actual_args = event.get_num_args()
            schema_types = self.schema.get_types(event.name)
            num_expected_args = len(schema_types)
            if num_expected_args != num_actual_args:
                raise Exception(f'The event {event.name} has a different number of args than specified in the schema')
            mapped_event = list(event.args)
            new_args = []
            for arg_idx, (arg, arg_type) in enumerate(zip(mapped_event, schema_types)):
                if type(arg) is not arg_type and arg_type is not str:
                    raise Exception(f'Type mismatch for event {event.name}. Expected {arg_type} for arg {arg_idx}, got {type(arg)}.')
                elif arg_type is str:
                    new_args.append(str(arg))
                else:
                    new_args.append(arg)
            events[idx].args = tuple(new_args)
    
    @abstractmethod
    def log(self, events : List[Event], event : threading.Event, flag_q : bool) -> Union[None, Tuple[bool, bool, Set[str], Set[str]]]:
        """Send events to enforcer(s) and return their processing results - must be implemented by subclasses"""
        pass
    
    @abstractmethod
    def parse_event(self, name : str, args : Tuple[str, ...], cmd : str, enforcer_name : str = None) -> None:
        """Parse event and update state - must be implemented by subclasses"""
        pass
    
    @abstractmethod
    def clean_cache(self) -> None:
        """Clean outdated cache entries - must be implemented by subclasses"""
        pass


class Logger(BaseLogger):

    def __init__(self, pep : PEP, schema : Schema, pdp : PDP, cache_timeout : int = 10):
        super().__init__(pep, schema, cache_timeout)
        self.pdp = pdp
        self.pdp.pep = pep
        self.proc = self.pdp.ocaml_proc
        self.write_prio = self.pdp.write_prio  # priority queue
        self.timer = self.pdp.timer
        self.cache : Dict[Tuple[Event, ...], Tuple[float, Tuple[bool, bool, Set[str], Set[str]]]]
        self.cache = {}
    
    def extend_mapping(self, pep : PEP) -> None:
        super().extend_mapping(pep)
        self.pdp.pep = self.pep

    def cache_update(self, events: List[Event], ts: float, result: Tuple[bool, bool, Set[str], Set[str]]) -> None:
        """
        update the cache with the given events, timestamp and result
        """
        events_key: Tuple[Event, ...] = self.make_cache_key(events)
        self.cache[events_key] = (ts, result)

    def cache_get(self, events: List[Event], curr_ts: float=time()) -> Union[None, Tuple[bool, bool, Set[str], Set[str]]]:
        """
        get the cached result for the given events
        """
        events_key: Tuple[Event, ...] = self.make_cache_key(events)
        if events_key in self.cache:
            ts, result = self.cache[events_key]
            if ts + self.cache_timeout > curr_ts:
                return result
            else:
                return None
        else:
            return None

    def clean_cache(self) -> None:
        """
        clean outdated cache entries from the logger cache
        """
        for k, (ts, _) in list(self.cache.items()):
            if ts + self.cache_timeout < time():
                del self.cache[k]

                
    """
    generate events to be sent to the priority queue and returns result of their processing: 
    cau_flag, sup_flag : if causation or suppression was triggered 
    cau_events, sup_events: the event names of the triggered events (args stored in self.sup_enc/self.cau_enc)
    """
    def log(self, events : List[Event], event : threading.Event, flag_q : bool) -> Union[None, Tuple[bool, bool, Set[str], Set[str]]]:
        ts = time()
        events = list(set(events))
        if random() < 0.01: 
            self.clean_cache()
        cached = self.cache_get(events, ts)
        if cached is not None:
            event.set()
            return cached
        events = list(set(events))
        self.check_type(events)
        all_events = ' '.join(map(str, events))        
        cau_flag = False
        sup_flag = False
        singleQueue : Queue = Queue()
        with self.timer.current_time_lock:
            stm = self.pdp.ts_bytes((all_events), self.timer.current_time, flag_q)
            tsp = self.timer.current_time
            event_flag = threading.Event()
            item = TimedTuple(tsp + 0.1, (event_flag, singleQueue, stm))
            self.write_prio.put(item)
        event_flag.wait()
        cau_flag, sup_flag = self.get_command(cau_flag, sup_flag, singleQueue)    
        event.set()
        result = (cau_flag, sup_flag, self.cau_events, self.sup_events)
        self.cache_update(events, ts, result) # cache the result
        return result
    
    def get_command(self, cau_flag : bool, sup_flag : bool, singleQueue : Queue) -> Tuple[bool, bool]:
        self._reset()
        while not singleQueue.empty():
            stms = singleQueue.get()
            while not stms.empty():
                msg = stms.get()
                for cau_event in msg.get("cause", {}):
                    name = cau_event["name"]
                    args = cau_event["args"]
                    cau_flag = True
                    self.parse_event(name, args, 'Cause')
                for sup_event in msg.get("suppress", {}):
                    name = sup_event["name"]
                    args = sup_event["args"]
                    sup_flag = True
                    self.parse_event(name, args, 'Suppress')
        return cau_flag, sup_flag

    def parse_event(self, name : str, args : Tuple[str, ...], cmd : str, enforcer_name : str = None) -> None:
        """Parse event and update state (enforcer_name unused in single enforcer mode)"""
        args_tuple = self.parse_args(name, args)
        if cmd == 'Suppress':
            if name in self.pep.sup_event_map:
                if name not in self.sup_enc:
                    self.sup_enc[name] = [args_tuple]
                else:
                    self.sup_enc[name].append(args_tuple)
                self.sup_events.add(name)
            else:
                raise Exception(f'No suppression handler defined for suppressed event {name}')
        if cmd == 'Cause':
            if name in self.pep.cau_event_map: 
                if name not in self.cau_enc:
                    self.cau_enc[name] = [args_tuple]
                else:
                    self.cau_enc[name].append(args_tuple)
                self.cau_events.add(name)
            else:
                raise Exception(f'No causation handler defined for caused event {name}')
    
    def clean_cache(self) -> None:
        """Clean outdated cache entries from the logger cache"""
        for k, (ts, _) in list(self.cache.items()):
            if ts + self.cache_timeout < time():
                del self.cache[k]


class MultiLogger(BaseLogger):
    """
    Logger for MultiPDP that broadcasts events to multiple enforcers and aggregates their responses.
    Uses OR logic: suppress if ANY enforcer says suppress, cause if ANY says cause.
    """
    
    def __init__(self, pep : PEP, schema : Schema, multi_pdp, cache_timeout : int = 10):
        from instrlib.pdp import MultiPDP
        
        super().__init__(pep, schema, cache_timeout)
        self.multi_pdp : MultiPDP = multi_pdp
        self.multi_pdp.pep = pep
        self._sup_enc_sets : Dict[str, Set[Tuple[Any, ...]]] = {}
        self._cau_enc_sets : Dict[str, Set[Tuple[Any, ...]]] = {}
        self.event_to_enforcers : Dict[str, List[Tuple[str, PDP]]] = {}
        self.partition_label_by_enforcer : Dict[str, str] = {}
        self.last_partition_wait_ms : Dict[str, float] = {}
        self.last_partition_merge_ms : Dict[str, float] = {}
        self.last_slowest_partition : Union[None, Tuple[str, float]] = None
        self.last_slowest_wait_partition : Union[None, Tuple[str, float]] = None
        self._batch_id : int = 0
        
        # Per-enforcer state
        self.enforcers_state : Dict[str, Dict] = {}
        for name, pdp in self.multi_pdp.get_all_enforcers():
            self.enforcers_state[name] = {
                'sup_events': set(),
                'cau_events': set(),
                'sup_enc': {},
                'cau_enc': {},
                'write_prio': pdp.write_prio,
                'timer': pdp.timer,
                'cache': {},
                'pdp': pdp,
            }

            formula_path = getattr(pdp, 'formula', None)
            if isinstance(formula_path, str) and formula_path.strip() != "":
                self.partition_label_by_enforcer[name] = os.path.basename(formula_path)
            else:
                self.partition_label_by_enforcer[name] = f"{name}.mfotl"

            allowed_events = getattr(pdp, 'allowed_events', None)
            if allowed_events is None and hasattr(pdp, 'accepts_event'):
                allowed_events = [event_name for event_name in self.schema.mapping if pdp.accepts_event(event_name)]
            if allowed_events is not None:
                for event_name in allowed_events:
                    if event_name not in self.event_to_enforcers:
                        self.event_to_enforcers[event_name] = []
                    self.event_to_enforcers[event_name].append((name, pdp))

    def _materialize_aggregated_encodings(self) -> None:
        """Convert internal set-based aggregation to list form for downstream consumers."""
        self.sup_enc = {name: list(args_set) for name, args_set in self._sup_enc_sets.items()}
        self.cau_enc = {name: list(args_set) for name, args_set in self._cau_enc_sets.items()}
    
    def _reset(self):
        """Reset aggregated state and per-enforcer state"""
        super()._reset()
        self._sup_enc_sets = {}
        self._cau_enc_sets = {}
        # Also reset per-enforcer state
        for name in self.enforcers_state:
            self.enforcers_state[name]['sup_events'] = set()
            self.enforcers_state[name]['cau_events'] = set()
            self.enforcers_state[name]['sup_enc'] = {}
            self.enforcers_state[name]['cau_enc'] = {}
    
    def extend_mapping(self, pep : PEP) -> None:
        super().extend_mapping(pep)
        self.multi_pdp.pep = self.pep
        # Update pep for all enforcers
        for _, pdp in self.multi_pdp.get_all_enforcers():
            pdp.pep = self.pep
    
    def log(self, events : List[Event], event : threading.Event, flag_q : bool) -> Union[None, Tuple[bool, bool, Set[str], Set[str]]]:
        """
        Broadcast events to all enforcers in parallel and aggregate responses.
        Events are filtered per enforcer based on their signature file.
        Returns: (cau_flag, sup_flag, cau_events, sup_events)
        """
        ts = time()
        self._batch_id += 1
        batch_id = self._batch_id
        events = list(set(events))
        
        # Check cache (use first enforcer's cache for simplicity)
        if self.enforcers_state and random() < 0.01:
            self.clean_cache()
        
        self.check_type(events)
        
        # Broadcast to all enforcers in parallel
        enf_queues : Dict[str, Queue] = {}
        enf_events : Dict[str, TimedCompletionEvent] = {}
        enf_enqueue_perf : Dict[str, float] = {}

        events_by_enforcer : Dict[str, List[Event]] = {}
        for ev in events:
            for name, _ in self.event_to_enforcers.get(ev.name, []):
                if name not in events_by_enforcer:
                    events_by_enforcer[name] = []
                events_by_enforcer[name].append(ev)

        for name, filtered_events in events_by_enforcer.items():
            if not filtered_events:
                continue

            state = self.enforcers_state[name]
            pdp = state['pdp']
            
            all_events = ' '.join(map(str, filtered_events))

            singleQueue = Queue()
            enf_queues[name] = singleQueue
            
            with state['timer'].current_time_lock:
                stm = pdp.ts_bytes(all_events, state['timer'].current_time, flag_q)
                tsp = state['timer'].current_time
                event_flag = TimedCompletionEvent()
                enf_events[name] = event_flag
                item = TimedTuple(tsp + 0.1, (event_flag, singleQueue, stm), batch_id=batch_id)
                state['write_prio'].put(item)
                enf_enqueue_perf[name] = perf_counter()
        
        # Wait for all enforcers to respond
        self.last_partition_wait_ms = {}
        self.last_slowest_wait_partition = None
        for name, event_flag in enf_events.items():
            event_flag.wait()

            enqueue_perf = enf_enqueue_perf.get(name)
            done_perf = event_flag.done_perf
            if isinstance(enqueue_perf, float) and isinstance(done_perf, float):
                wait_ms = max(0.0, (done_perf - enqueue_perf) * 1000.0)
            else:
                wait_ms = 0.0
            self.last_partition_wait_ms[name] = wait_ms

        if self.last_partition_wait_ms:
            slow_wait_name, slow_wait_ms = max(self.last_partition_wait_ms.items(), key=lambda kv: kv[1])
            self.last_slowest_wait_partition = (slow_wait_name, slow_wait_ms)
            wait_timings = ", ".join(
                f"{self.partition_label_by_enforcer.get(name, name)}={ms:.3f}ms"
                for name, ms in sorted(self.last_partition_wait_ms.items(), key=lambda kv: kv[1], reverse=True)
            )
            slow_wait_label = self.partition_label_by_enforcer.get(slow_wait_name, slow_wait_name)
            _print(
                "reader",
                "multi",
                f"[MultiLoggerTiming] wait_batch batch_id={batch_id} partitions={len(self.last_partition_wait_ms)} "
                f"slowest={slow_wait_label}:{slow_wait_ms:.3f}ms waits=[{wait_timings}]",
            )
        
        # Aggregate responses using OR logic
        self._reset()
        cau_flag = False
        sup_flag = False
        self.last_partition_merge_ms = {}
        self.last_slowest_partition = None
        
        for name, singleQueue in enf_queues.items():
            part_start = perf_counter()
            enf_cau_flag, enf_sup_flag = self.get_command_from_enforcer(name, singleQueue)
            part_ms = (perf_counter() - part_start) * 1000.0
            self.last_partition_merge_ms[name] = part_ms
            cau_flag = cau_flag or enf_cau_flag
            sup_flag = sup_flag or enf_sup_flag

        if self.last_partition_merge_ms:
            slow_name, slow_ms = max(self.last_partition_merge_ms.items(), key=lambda kv: kv[1])
            self.last_slowest_partition = (slow_name, slow_ms)
            timings = ", ".join(
                f"{self.partition_label_by_enforcer.get(name, name)}={ms:.3f}ms"
                for name, ms in sorted(self.last_partition_merge_ms.items(), key=lambda kv: kv[1], reverse=True)
            )
            slow_label = self.partition_label_by_enforcer.get(slow_name, slow_name)
            _print(
                "reader",
                "multi",
                f"[MultiLoggerTiming] merge_batch batch_id={batch_id} partitions={len(self.last_partition_merge_ms)} "
                f"slowest={slow_label}:{slow_ms:.3f}ms timings=[{timings}]",
            )

        self._materialize_aggregated_encodings()
        
        event.set()
        result = (cau_flag, sup_flag, self.cau_events, self.sup_events)
        return result
    
    def get_command_from_enforcer(self, enforcer_name : str, singleQueue : Queue) -> Tuple[bool, bool]:
        """Process commands from a specific enforcer"""
        state = self.enforcers_state[enforcer_name]
        cau_flag = False
        sup_flag = False
        
        while not singleQueue.empty():
            stms = singleQueue.get()
            while not stms.empty():
                msg = stms.get()
                for cau_event in msg.get("cause", {}):
                    name = cau_event["name"]
                    args = cau_event["args"]
                    cau_flag = True
                    self.parse_event(name, args, 'Cause', enforcer_name)
                for sup_event in msg.get("suppress", {}):
                    name = sup_event["name"]
                    args = sup_event["args"]
                    sup_flag = True
                    self.parse_event(name, args, 'Suppress', enforcer_name)
        
        return cau_flag, sup_flag
    
    def parse_event(self, name : str, args : Tuple[str, ...], cmd : str, enforcer_name : str) -> None:
        """Parse event and update both per-enforcer and aggregated state"""
        args_tuple = self.parse_args(name, args)
        state = self.enforcers_state[enforcer_name]
        
        if cmd == 'Suppress':
            if name in self.pep.sup_event_map:
                # Update aggregated state
                if name not in self._sup_enc_sets:
                    self._sup_enc_sets[name] = set()
                self._sup_enc_sets[name].add(args_tuple)
                self.sup_events.add(name)
                
                # Update per-enforcer state
                if name not in state['sup_enc']:
                    state['sup_enc'][name] = set()
                state['sup_enc'][name].add(args_tuple)
                state['sup_events'].add(name)
            else:
                raise Exception(f'No suppression handler defined for suppressed event {name}')
        
        if cmd == 'Cause':
            if name in self.pep.cau_event_map:
                # Update aggregated state
                if name not in self._cau_enc_sets:
                    self._cau_enc_sets[name] = set()
                self._cau_enc_sets[name].add(args_tuple)
                self.cau_events.add(name)
                
                # Update per-enforcer state
                if name not in state['cau_enc']:
                    state['cau_enc'][name] = set()
                state['cau_enc'][name].add(args_tuple)
                state['cau_events'].add(name)
            else:
                raise Exception(f'No causation handler defined for caused event {name}')
    
    def clean_cache(self) -> None:
        """Clean outdated cache entries for all enforcers"""
        for name in self.enforcers_state:
            cache = self.enforcers_state[name]['cache']
            for k, (ts, _) in list(cache.items()):
                if ts + self.cache_timeout < time():
                    del cache[k]