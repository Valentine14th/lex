from itertools import chain
from typing import Any, Dict, Tuple, Union

from instrlib.handler_graph import generate_graph

class Mapping:

    def __init__(
        self, 
        mapping       : Dict[Tuple[str, str], Any]       = {},
        sup_event_map : Dict[Union[str, Tuple[str, ...]], Any] = {}, 
        cau_event_map : Dict[Union[str, Tuple[str, ...]], Any] = {},
    ):
        self.mapping : Dict[Tuple[str, str], Any] = {}
        if isinstance(mapping, dict):
            for (key, f) in mapping.items():
                self.populate(key, f)
        self.sup_event_map = sup_event_map
        self.cau_event_map = cau_event_map
        self.sup_graph     = generate_graph(self.sup_event_map)
        self.cau_graph     = generate_graph(self.cau_event_map)

    def __or__(self, other : "Mapping") -> "Mapping":
        return Mapping(
            mapping       = dict(chain(self.mapping.items(),       other.mapping.items())),
            sup_event_map = dict(chain(self.sup_event_map.items(), other.sup_event_map.items())),
            cau_event_map = dict(chain(self.cau_event_map.items(), other.cau_event_map.items())),
        )
    
    def populate(self, tuple : Tuple[str, str], f : Any) -> None:
        self.mapping[tuple] = f
    
    def __getitem__(self, key : Tuple[str, str]) -> Any:
        if key not in self.mapping:
            Exception(f'key {key} is not in InstrMapping')
        return self.mapping[key]

    def __iter__(self):
        return iter(self.mapping)
    
