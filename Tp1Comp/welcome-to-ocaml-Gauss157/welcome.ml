let main =
  print_string "What is your name? ";
  let n = read_line () in
  print_endline (Mylib.Hello.greeting n);

  print_string "In what year were you born? ";
  let _ = read_line () in

  print_endline "You are 22 years old.";