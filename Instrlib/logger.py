from queue import Queue
import threading
from typing import Tuple, List, Set, Union, Dict

from instrlib.enforcer import Enforcer
from instrlib.event import *
from instrlib.event import TimedTuple
from instrlib.mapping import Mapping
from instrlib.schema import Schema

class Logger:

    def __init__(self, mp : Mapping, schema : Schema, enforcer : Enforcer):
        self.mp                                            = mp 
        self.schema     : Schema                           = schema
        self.enforcer                                      = enforcer
        self.enforcer.mp                                   = mp
        for _, event in self.mp.mapping.items():            
            if event.name not in schema.mapping:
                Exception(f"Event {event} is not defined in the schema.") 
        self.sup_events : Set[str]                         = set() #used to store suppressed event names 
        self.cau_events : Set[str]                         = set() #used to store caused event names
        self.sup_enc    : Dict[str, List[Tuple[Any, ...]]] = {}    #used to store suppression cmds returned by the enforcer
        self.cau_enc    : Dict[str, List[Tuple[Any, ...]]] = {}    #used to store causation cmds returned by the enforcer
        self.proc                                          = self.enforcer.ocaml_proc
        self.write_prio                                    = self.enforcer.write_prio #priority queue
        self.timer                                         = self.enforcer.timer

    def _reset(self):
        self.sup_events = set()
        self.cau_events = set()
        self.sup_enc    = {}
        self.cau_enc    = {}

    def extend_mapping(self, mp : Mapping) -> None:
        self.mp          = self.mp | mp
        self.enforcer.mp = self.mp

    def extend_schema(self, schema : Schema) -> None:
        self.schema = self.schema | schema
                
    """
    generate events to be sent to the priority queue and returns result of their processing: 
    cau_flag, sup_flag : if causation or suppression was triggered 
    cau_events, sup_events: the event names of the triggered events (args stored in self.sup_enc/self.cau_enc)
    """
    def log(self, events : List[Event], event : threading.Event, flag_q : bool) -> Union[None, Tuple[bool, bool, Set[str], Set[str]]]:
        self.check_type(events)
        all_events = ' '.join(map(str, events))        
        cau_flag = False
        sup_flag = False
        singleQueue : Queue = Queue()
        with self.timer.current_time_lock:
            stm = self.enforcer.ts_bytes((all_events), self.timer.current_time, flag_q)
            tsp = self.timer.current_time
            event_flag = threading.Event()
            item = TimedTuple(tsp + 0.1, (event_flag, singleQueue, stm))
            self.write_prio.put(item)
        event_flag.wait()
        cau_flag, sup_flag = self.get_command(cau_flag, sup_flag, singleQueue)    
        event.set()
        return cau_flag, sup_flag, self.cau_events, self.sup_events
    
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

    def parse_args(self, name : str, args : Tuple[str, ...]) -> Tuple[Any, ...]:
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

    def parse_event(self, name : str, args : Tuple[str, ...], cmd : str) -> None:
        args_tuple = self.parse_args(name, args)
        if cmd == 'Suppress':
            if name in self.mp.sup_event_map:
                if name not in self.sup_enc:
                    self.sup_enc[name] = [args_tuple]
                else:
                    self.sup_enc[name].append(args_tuple)
                self.sup_events.add(name)
            else:
                raise Exception(f'No suppression handler defined for suppressed event {name}')
        if cmd == 'Cause':
            if name in self.mp.cau_event_map: 
                if name not in self.cau_enc:
                    self.cau_enc[name] = [args_tuple]
                else:
                    self.cau_enc[name].append(args_tuple)
                self.cau_events.add(name)
            else:
                raise Exception(f'No causation handler defined for caused event {name}')

    """
    check for each event that the event is defined through the schema and 
    has the same numer and type as defined in the schema 
    """
    def check_type(self, events : List[Event]):
         for idx, event in enumerate(events):
            # print('current event', event)
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