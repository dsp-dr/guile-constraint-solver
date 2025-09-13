#!/usr/bin/env guile
#!/usr/bin/env guile
!#

(use-modules (ice-9 popen)
             (ice-9 textual-ports))

(define (run-lean-examples)
  "Run Lean examples and capture output"
  (let* ((port (open-pipe* OPEN_READ "lake build && lake exe examples"))
         (output (get-string-all port)))
    (close-pipe port)
    output))

(define (run-guile-examples)
  "Run Guile examples and capture output"
  (system "sh run-examples.sh"))

(display "=== Comparing Guile and Lean4 Solutions ===\n\n")
(display "Running Guile examples...\n")
(run-guile-examples)
(display "\nRunning Lean4 examples...\n")
(display (run-lean-examples))
