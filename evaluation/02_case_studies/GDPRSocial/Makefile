PYTHON   ?= python3
ENFGUARD ?= ~/Git/whyenf/enfguard
LOG      ?= log
STATE    ?= enfflash.state
SIG      ?= policies/minitwit_gdpr.sig
FORMULA  ?= policies/minitwit_gdpr.mfotl
FUNC     ?= policies/gdpr.py

.PHONY: clean run monitor all

# Remove log and state, then start the server with --clean to reset enforcement state
clean:
	rm -f $(LOG) $(STATE)
	$(PYTHON) manage.py runserver --noreload --clean

# Replay the current log using the enforcement monitor (run in a separate terminal)
replay:
	clear
	$(ENFGUARD) -formula $(FORMULA) -sig $(SIG) -func $(FUNC) -log $(LOG) -state $(STATE) -label

replay_v:
	clear
	$(ENFGUARD) -formula $(FORMULA) -sig $(SIG) -func $(FUNC) -log $(LOG) -state $(STATE) -label -verbose 1

# Start the Django server (without --clean, for use after monitor is running)
run:
	$(PYTHON) manage.py runserver --noreload

# Convenience: clean + run in one step
all: clean
