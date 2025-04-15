Lex - A Language for Compliance by Design
=========================================

![Lex Logo](Logo.png "lex")

# Table of Contents
- [Lex - A language for Compliance by Design](#lex---a-language-for-compliance-by-design)
- [Table of Contents](#table-of-contents)
- [Repository Overview](#repository-overview)
- [Installation](#installation)
  - [VS Code Dev Container](#vs-code-dev-container)
    - [Requirements:](#requirements)
    - [Using Lex with devcontainer](#using-lex-with-devcontainer)
      - [Setting up the devcontainr](#setting-up-the-devcontainr)
      - [Start using the devcontainer](#start-using-the-devcontainer)
  - [Build from source](#build-from-source)
    - [requirements](#requirements-1)
- [Usage](#usage)
  - [Setting up the environment](#setting-up-the-environment)
  - [Without installing Lex](#without-installing-lex)
  - [With installation](#with-installation)

# Repository Overview

This repository contains:
- A copy of the [EnfGuard](https://github.com/runtime-enforcement/enfguard) tool in a submodule `enfguard` (update it with `git submodule update --init --recursive` before using Lex)
- The Instrlib library (`Instrlib/`)
- The source code of Lex (`src/` and `bin/`)
- A VS Code extension providing code coloring for Lex (`vscode/lex`)
- Documentation for Lex (`doc/`) including a cheatsheet, a syntax manual, and the tutorial used in our user study (RQ4)
- Examples of Lex and Rex code (`example/`): `BGG` (RQ1), `GDPR` (RQ1-3, including Rex code for Shynet and Minitwitter), `IRC` (RQ1), `user_study` (RQ4/auditing), `tutorial` (code of the tutorial), `unit` (basic examples)
- The code of our case studies (`case_studies.zip`, RQ2-3)
- The survey used in our user study (`user_study/`)

# Installation
## VS Code Dev Container
### Requirements:
- [Docker](https://www.docker.com/)
- [VS Code](https://code.visualstudio.com/)
    - [Remote Explorer](https://marketplace.visualstudio.com/items?itemName=ms-vscode.remote-explorer) extension (In VS Code, press`ctrl` + `shift` + `x`, then search for "Remote Explorer" and install the extension)

### Using Lex with devcontainer
#### Setting up the devcontainr
- Open this repository in VS Code
- Press `ctrl`+`shift`+`p` and search for "remote explorer: Focus on Dev Containers View"

![alt text](images/remote-explorer-focus-view.png)

- Inside the window pane that appeared click on the button to open the current folder in a dev container

![alt text](images/remote-explorer-panel.png)

- This might take a few minutes to set up the container

#### Start using the devcontainer
See the [setting-up-the-environment](#setting-up-the-environment) section for instructions on how to set up the vscode environemnt and install the Lex-language extension

Refer to the [usage](#usage) chapter for further instructions on using Lex

## Build from source
### requirements
- [Ocaml](https://ocaml.org/docs/installing-ocaml)

Set the Ocaml version:

```bash
opam switch create 4.14.0
eval $(opam env)
```
Install project dependencies:
```bash
opam install . --deps-only
eval $(opam env)
```

Optionally install a language server (for development only):
```bash
opam install ocaml-lsp-server ocamlformat
```


To build the project run the following command:
```bash
dune build
```

# Usage
## Setting up the environment

To install the VS Code extension for syntax highlighting in `.lex` files, run:
```bash
code --install-extension vscode/lex/lex-0.0.1.vsix
```

To build and package the extension again see the [README](vscode/lex/README.md) in the vscode/lex directory

## Without installing Lex
From the root directory of this repository, run:
```bash
./bin/main.exe <path/to/.lex file> [-mode (mfotl|doc)]
```
`-mode doc` will compile a lex program to a human readable html file.

e.g.
```bash
./bin/main.exe examples/unit/hello.lex
```

## With installation
Alternatively, Lex can be installed using opam:
In the root directory of this repository, run:
```bash
opam install .
```
Then you can run lex from anywhere in your terminal:
```bash
lex <path/to/.lex file> [-mode (mfotl|doc)]
```
