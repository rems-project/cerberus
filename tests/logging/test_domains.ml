let () =
  let run_workers count f = Concurrency_cases.run_workers ~spawn:Domain.spawn ~join:Domain.join ~relax:Domain.cpu_relax count f in
  Concurrency_cases.concurrent_misses ~run_workers ();
  Concurrency_cases.concurrent_severities ~run_workers ();
  Concurrency_cases.concurrent_output ~run_workers Cerb_log.Json;
  Concurrency_cases.concurrent_output ~run_workers Cerb_log.Text;
  print_endline "Concurrent registration and output passed (domains)"
