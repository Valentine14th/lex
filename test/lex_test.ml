(* filepath: /home/jnz/lex/test/lex_test.ml *)
let test_example () =
  Alcotest.(check int) "example test" 4 (2 + 2)

let () =
  Alcotest.run "Lex Tests" [
    "Example Suite", [
      Alcotest.test_case "Example Test" `Quick test_example;
    ];
  ]