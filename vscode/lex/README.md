# lex README

- [lex README](#lex-readme)
  - [To package and install the extension:](#to-package-and-install-the-extension)


## To package and install the extension:
make sure `vsce` is installed:
```sh
npm install -g @vscode/vsce
```

```sh
vsce package
code --install-extension lex-0.0.1.vsix
```