;;; core/constraint-engine.scm --- Native constraint propagation engine

(define-module (core constraint-engine)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-26)
  #:use-module (ice-9 match)
  #:export (<domain> make-domain domain? domain-values
            <variable> make-variable variable? variable-name variable-domain
            <constraint> make-constraint constraint? 
            constraint-variables constraint-predicate
            solve-csp
            all-different-constraint
            sum-constraint))

;; Domain representation
(define-record-type <domain>
  (make-domain values)
  domain?
  (values domain-values set-domain-values!))

;; Variable representation
(define-record-type <variable>
  (make-variable name domain)
  variable?
  (name variable-name)
  (domain variable-domain))

;; Constraint representation
(define-record-type <constraint>
  (make-constraint variables predicate)
  constraint?
  (variables constraint-variables)
  (predicate constraint-predicate))

;; Constraint solver
(define (solve-csp variables constraints)
  "Simple backtracking constraint solver with constraint propagation"
  (define (consistent? assignment)
    (every (lambda (c)
             (let ((vars (constraint-variables c))
                   (pred (constraint-predicate c)))
               (if (every (cut assoc <> assignment) vars)
                   (apply pred (map (cut assoc-ref assignment <>) vars))
                   #t)))
           constraints))
  
  (define (select-unassigned-variable assignment)
    ;; MRV heuristic: choose variable with smallest domain
    (let ((unassigned (filter (lambda (v) (not (assoc v assignment))) variables)))
      (and (not (null? unassigned))
           (fold (lambda (v best)
                   (if (< (length (domain-values (variable-domain v)))
                          (length (domain-values (variable-domain best))))
                       v best))
                 (car unassigned)
                 (cdr unassigned)))))
  
  (define (backtrack assignment)
    (if (= (length assignment) (length variables))
        assignment  ; Solution found
        (let ((var (select-unassigned-variable assignment)))
          (and var
               (any (lambda (value)
                      (let ((new-assignment (cons (cons var value) assignment)))
                        (and (consistent? new-assignment)
                             (backtrack new-assignment))))
                    (domain-values (variable-domain var)))))))
  
  (backtrack '()))

;; Common constraints
(define (all-different-constraint vars)
  "All variables must have different values"
  (make-constraint vars
    (lambda values
      (= (length values) (length (delete-duplicates values))))))

(define (sum-constraint vars target)
  "Sum of variables must equal target"
  (make-constraint vars
    (lambda values
      (= (apply + values) target))))
