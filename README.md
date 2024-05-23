# Lex

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
- In the container, open a terminal window (`ctrl`+`` ` ``)
    - Run `dune build` to compile the project
    - To install the VS Code extension for syntax highlighting in `.lex` files, run:
    - `code --install-extension vscode/lex/lex-0.0.1.vsix`

Refer to the Usage chapter for further instructions


### Build from source
#### requirements
- ocaml (https://ocaml.org/docs/installing-ocaml)

Install the following libraries using opam
```bash
opam install dune core_unix menhir xml-light ppx_jane ocaml-lsp-server calendar
eval $(opam env)
```

To build the project run the following command:
```bash
dune build
```

## Usage
From the root directory of this repository, run:
```bash
./bin/main.exe <path/to/.lex file> [-mode (mfotl|doc)]
```
`-mode doc` will compile a lex program to a human readable html file.

e.g.
```bash
./bin/main.exe examples/hello.lex
```


