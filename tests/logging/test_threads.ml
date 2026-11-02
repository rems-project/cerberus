let () =
  let run_workers count f = Concurrency_cases.run_threads count f in
  Concurrency_cases.concurrent_misses ~run_workers ();
  Concurrency_cases.concurrent_severities ~run_workers ();
  Concurrency_cases.concurrent_output ~run_workers ();
  print_endline "Concurrent registration and output passed (threads)"
