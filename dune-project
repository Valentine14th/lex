(lang dune 3.13)

(name lex)

(using menhir 3.0)

(generate_opam_files true)

(authors "François Hublet" "Jonas Degelo")

(maintainers "François Hublet" "Jonas Degelo")

(license LICENSE)

(documentation https://url/to/documentation)

; (map_workspace_root false) ; https://github.com/ocamllabs/vscode-ocaml-platform#debugging-ocaml-programs-experimental

(package
  (name lex)
  (synopsis "Compiling the law into logic")
  (description "Compiling the law into logic")
  (depends
    (ocaml (>= 4.14))
    core_unix
    menhir
    xml-light
    ppx_jane
    calendar
    z3
    pyml
    alcotest
  )
  (allow_empty))
