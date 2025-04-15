Lex - A Language for Compliance by Design
=========================================

![Lex Logo](Logo.png "lex")

# Table of Contents
- [Lex - A language for formalizing legal texts](#lex---a-language-for-formalizing-legal-texts)
- [Table of Contents](#table-of-contents)
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
- [known issues](#known-issues)

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
./bin/main.exe examples/hello.lex
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
