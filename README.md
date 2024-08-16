# Lex

- [Lex](#lex)
  - [Installation](#installation)
    - [VS Code Dev Container](#vs-code-dev-container)
      - [Prerequisites:](#prerequisites)
      - [Using Lex with devcontainer](#using-lex-with-devcontainer)
    - [Build from source](#build-from-source)
      - [requirements](#requirements)
  - [Usage](#usage)
    - [Without installing Lex](#without-installing-lex)
    - [With installation](#with-installation)

## Installation
### VS Code Dev Container
#### Prerequisites:
- Docker
- VS Code
    - Remote Explorer extension (In VS Code, press`ctrl` + `shift` + `x`, then search for "Remote Explorer" and install the extension)

#### Using Lex with devcontainer
- Open this repository in VS Code
- Press `ctrl`+`shift`+`p` and search for "remote explorer: Focus on Dev Containers View"
- Inside the window pane that appeared click on the button to open the current folder in a dev container
- This might take a few minutes to set up the container
- In the container, open a terminal window
    - Run `dune build` to compile the project
    - To install the VS Code extension for syntax highlighting in `.lex` files, run:
    - `code --install-extension vscode/lex/lex-0.0.1.vsix`

Refer to the Usage chapter for further instructions


### Build from source
#### requirements
- Ocaml (https://ocaml.org/docs/installing-ocaml)

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

## Usage
### Without installing Lex
From the root directory of this repository, run:
```bash
./bin/main.exe <path/to/.lex file> [-mode (mfotl|doc)]
```
`-mode doc` will compile a lex program to a human readable html file.

e.g.
```bash
./bin/main.exe examples/hello.lex
```

### With installation
Alternatively, Lex can be installed using opam:
In the root directory of this repository, run:
```bash
opam install .
```
Then you can run lex from anywhere in your terminal:
```bash
lex <path/to/.lex file> [-mode (mfotl|doc)]
```


