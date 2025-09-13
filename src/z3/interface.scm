;;; z3/interface.scm --- Z3 SMT solver interface for Guile

(define-module (z3 interface)
  #:use-module (ice-9 popen)
  #:use-module (ice-9 textual-ports)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:export (z3-solve
            parse-z3-model
            make-smt-var
            smt-assert
            smt-minimize
            smt-maximize))

(define (z3-solve smt-code)
  "Send SMT-LIB2 code to Z3 and return result"
  (let* ((port (open-pipe* OPEN_BOTH "z3" "-in"))
         (result (begin
                   (display smt-code port)
                   (force-output port)
                   (let ((response (get-string-all port)))
                     (close-pipe port)
                     response))))
    result))

(define (parse-z3-model output)
  "Parse Z3 model output into an alist"
  (let ((lines (string-split output #\newline)))
    (filter-map
     (lambda (line)
       (match (string-split line #\space)
         (("(define-fun" name "()" type value ")")
          (cons (string->symbol name)
                (cond ((string=? value "true") #t)
                      ((string=? value "false") #f)
                      ((string->number value) => identity)
                      (else value))))
         (_ #f)))
     lines)))

(define (make-smt-var name type)
  "Generate SMT variable declaration"
  (format #f "(declare-const ~a ~a)" name type))

(define (smt-assert expr)
  "Generate SMT assertion"
  (format #f "(assert ~a)" expr))

(define (smt-minimize expr)
  "Generate SMT minimize objective"
  (format #f "(minimize ~a)" expr))

(define (smt-maximize expr)
  "Generate SMT maximize objective"
  (format #f "(maximize ~a)" expr))
