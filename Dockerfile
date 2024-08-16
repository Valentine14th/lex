FROM ocaml/opam:debian-ocaml-4.13

COPY --chown=opam:opam ./ /home/opam/lex

# COPY --chown=opam:opam ./vscode/lex /home/opam/.vscode/extensions/lex

WORKDIR /home/opam/lex

# RUN code --install-extension /home/opam/lex/vscode/lex/lex-0.0.1.vsix

RUN opam install . --deps-only \
    && opam install ocaml-lsp-server \
    && eval $(opam env) \
    && dune build