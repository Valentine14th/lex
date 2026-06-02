from threading import Lock, Event
import json

class Timer:

    def __init__(self, state_file : str | None = None):
        self.current_time      = 0
        self.current_time_lock = Lock()
        self.timerflag         = Event()
        self.first_time        = True
        if state_file is not None:
            self._set_time_from_file(state_file)

    def _set_time_from_file(self, state_file : str):
        if state_file is not None:
            try:
                with open(state_file, 'r') as f:
                    state = json.load(f)
                    self.current_time = state.get('last_proactive_ts', -1) + 1
            except Exception as e:
                print("timer", f"Failed to load timer state: {e}")