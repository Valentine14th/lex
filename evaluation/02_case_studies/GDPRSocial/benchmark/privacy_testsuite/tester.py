import os.path
import traceback

from tqdm import tqdm

class Tester:

    DEFAULT_N = 2
    
    def __init__(self, title, App, Reporter, root_folder, policy, exe, instrlib=None, formula=None, sig=None):
        self.App = App
        self.Reporter = Reporter
        self.title = title
        self.root_folder = root_folder
        self.reporter = None
        self._report_folder = None
        self.policy = policy
        self.exe = exe
        self.instrlib = instrlib
        self.formula = formula
        self.sig = sig

    def _save_progress(self, data, folder, app):
        self.reporter = self.Reporter(self.title, list(data), app.dep_vars(), app.indep_vars())
        if folder is not None:
            if self._report_folder is not None:
                self.reporter.folder = self._report_folder
            self.reporter.save(folder)
            self._report_folder = self.reporter.folder
        
    def test(self, N=DEFAULT_N, folder=None):
        data = []
        self._report_folder = None
        app = self.App()
        app.start(self.policy, self.exe, self.instrlib, formula=self.formula, sig=self.sig)
        try:
            configs = app.configurations()
            cs = [(config, scenario)
                  for config in configs
                  for scenario in app.scenarios(self.policy, config=config)]
            for (config, scenario) in tqdm(cs):
                initialized = False
                try:
                    scenario.initialize(config)
                    initialized = True
                    for measurement_idx in range(N):
                        try:
                            result = scenario.run()
                            if isinstance(result, dict) and all(key in result for key in ['sc', 'u', 'n', 't']):
                                data.append(result)
                            else:
                                print(
                                    f"Invalid result for scenario {scenario.sc} with config {config} "
                                    f"at measurement {measurement_idx + 1}/{N}: {result}"
                                )
                            scenario.continue_()
                        except Exception:
                            print(
                                f"Scenario {scenario.sc} with config {config} failed at "
                                f"measurement {measurement_idx + 1}/{N}; continuing with next scenario."
                            )
                            traceback.print_exc()
                            break
                except Exception:
                    print(f"Scenario {scenario.sc} with config {config} failed during setup; continuing.")
                    traceback.print_exc()
                finally:
                    if initialized:
                        try:
                            scenario.finalize()
                        except Exception:
                            print(f"Scenario {scenario.sc} with config {config} failed during teardown; continuing.")
                            traceback.print_exc()
                    self._save_progress(data, folder, app)
        finally:
            app.stop()
        self.reporter = self.Reporter(self.title, data, app.dep_vars(), app.indep_vars())
        if folder is not None:
            if self._report_folder is not None:
                self.reporter.folder = self._report_folder
            self.reporter.save(folder)
            self._report_folder = self.reporter.folder
        self.N = N

    def load(self, N=DEFAULT_N):
        self.reporter = self.Reporter(self.title, data=os.path.join(self.root_folder))
        self.N = N
            
    def generate(self, baseline=None):
        assert(self.reporter is not None)
        self.reporter.generate(self.root_folder, N=self.N, baseline_folder=baseline)

