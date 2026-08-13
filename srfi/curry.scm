;; SPDX-FileCopyrightText: 2026 Scáth
;; SPDX-License-Identifier: MIT

;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use,
;;; copy, modify, merge, publish, distribute, sublicense, and/or
;;; sell copies of the Software, and to permit persons to whom the
;;; Software is furnished to do so, subject to the following
;;; conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
;;; OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;; FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;; OTHER DEALINGS IN THE SOFTWARE.

;;; https://curry-lang.org (github.com/deconstructo/curry) implementation.
;;;
;;; Written directly against curry's own primitives rather than reusing
;;; generic.scm: curry has no SRFI 14 (char-sets), SRFI 26 (cut), SRFI 160
;;; (numeric vectors), or SRFI 253 (checked lambdas), all of which
;;; generic.scm depends on. It does have SRFI 1, 69 (hash tables), 111
;;; (boxes), and 113 (sets/bags), which this file uses instead.
;;;
;;; Scope: object, number, boolean, pair, symbol, character, string,
;;; vector, bytevector, error-object, hash-table, box, set, bag, and
;;; record/record-type properties. Deliberately not covered, for the same
;;; reason generic.scm's dependencies are unavailable:
;;;   - procedure properties: curry has no procedure-name/arity/arglist
;;;     introspection exposed to Scheme.
;;;   - numeric-vector (s8vector etc.) properties: no SRFI 4/160.
;;;   - char-set properties: no SRFI 14.
;;;   - library/environment properties: curry's module registry has no
;;;     Scheme-level enumeration API.
;;;
;;; Record introspection (record?, record-rtd, record-type-name,
;;; record-type-field-names — (rnrs records inspection) naming) needed
;;; four small primitives curry didn't previously expose to Scheme at
;;; all (only the type-specific predicate/accessor closures
;;; define-record-type itself hands out); assumed present here, added in
;;; curry >= (whatever version ships this).
;;;
;;; Known limitation: curry's write/display have no cycle detection (no
;;; #n=/#n# datum labeling), so inspect-properties/inspect-describe will
;;; hang on any object containing a cycle, since object-properties below
;;; always calls write/display on the object itself first. Nothing in
;;; this file works around that; it's a core gap, not specific to this
;;; SRFI.

(define (%to-string-with object proc)
  (call-with-port (open-output-string)
    (lambda (p) (proc object p) (get-output-string p))))

(define (object-properties object)
  (list (list 'write   (%to-string-with object write))
        (list 'display (%to-string-with object display))))

;;; ---- Number ----

(define (number-properties object)
  (append
    (list (list 'real-part (real-part object))
          (list 'imag-part (imag-part object)))
    (if (rational? object)
        (list (list 'numerator (numerator object))
              (list 'denominator (denominator object))
              (list 'real-sign (cond ((negative? object) -1)
                                      ((zero? object) 0)
                                      (else 1)))
              (list 'real-base 2))
        '())
    (if (and (integer? object) (>= object 0) (<= object #x10FFFF))
        (list (list 'integer->char (integer->char (exact object))))
        '())
    (if (and (integer? object) (exact? object))
        (list (list 'display-2  (number->string object 2))
              (list 'display-8  (number->string object 8))
              (list 'display-16 (number->string object 16)))
        '())))

;;; ---- Boolean ----

(define (boolean-properties object)
  (list (list 'boolean->integer (if object 1 0))))

;;; ---- Pair ----
;;;
;;; `list?` is R7RS-guaranteed to be #f for both dotted and circular
;;; pairs, so it's the single check that safely gates every list-
;;; consuming property below -- a circular or dotted pair still gets
;;; car/cdr, just not the rest.

(define (indexed-properties lst)
  (let loop ((lst lst) (i 0) (acc '()))
    (if (null? lst)
        (reverse acc)
        (loop (cdr lst) (+ i 1) (cons (list i (car lst)) acc)))))

(define (pair-properties object)
  (append
    (list (list 'car (car object)) (list 'cdr (cdr object)))
    (if (list? object)
        (append
          (list (list 'last (car (last-pair object)))
                (list 'last-pair (last-pair object))
                (list 'length (length object)))
          (if (every char? object)
              (list (list 'list->string (list->string object)))
              '())
          (list (list 'list->vector (list->vector object)))
          (indexed-properties object))
        '())))

;;; ---- Symbol ----

(define (symbol-properties object)
  (list (list 'symbol->string (symbol->string object))))

;;; ---- Character ----

(define (char-properties object)
  (append
    (list (list 'char->integer (char->integer object)))
    (if (char-numeric? object)
        (let ((d (digit-value object)))
          (if d (list (list 'digit-value d)) '()))
        '())
    (list (list 'char-alphabetic? (char-alphabetic? object))
          (list 'char-numeric?    (char-numeric? object))
          (list 'char-whitespace? (char-whitespace? object))
          (list 'char-upper-case? (char-upper-case? object))
          (list 'char-lower-case? (char-lower-case? object)))))

;;; ---- String ----
;;;
;;; curry has no string->vector/vector->string (an independent gap) --
;;; small local fallbacks via the list conversions curry does have.

(define (%string->vector s) (list->vector (string->list s)))
(define (%vector->string v) (list->string (vector->list v)))

(define (string-properties object)
  (append
    (list (list 'string->symbol (string->symbol object))
          (list 'string->list   (string->list object))
          (list 'string->vector (%string->vector object))
          (list 'string->utf8   (string->utf8 object))
          (list 'string-length  (string-length object)))
    ;; (string->number "") incorrectly returns 0 rather than #f in some
    ;; curry builds (a core numeric-parser bug) -- guard the empty
    ;; string explicitly so that doesn't leak a bogus entry here.
    (if (> (string-length object) 0)
        (let ((n (string->number object)))
          (if n (list (list 'string->number n)) '()))
        '())
    (indexed-properties (string->list object))))

;;; ---- Vector ----

(define (vector-properties object)
  (append
    (list (list 'vector-length (vector-length object))
          (list 'vector->list (vector->list object)))
    (if (every char? (vector->list object))
        (list (list 'vector->string (%vector->string object)))
        '())
    (indexed-properties (vector->list object))))

;;; ---- Bytevector ----
;;;
;;; No guard around utf8->string: curry's utf8->string does a raw copy
;;; with no UTF-8 validation, so it always succeeds -- for a bytevector
;;; that isn't valid UTF-8 this entry is present but its content is
;;; garbled rather than a real decode.

(define (bytevector->list bv)
  (let loop ((i (- (bytevector-length bv) 1)) (acc '()))
    (if (< i 0) acc (loop (- i 1) (cons (bytevector-u8-ref bv i) acc)))))

(define (bytevector-properties object)
  (append
    (list (list 'utf8->string (utf8->string object)))
    (indexed-properties (bytevector->list object))))

;;; ---- Record ----

(define (record-field-properties names ref)
  (let loop ((names names) (i 0) (acc '()))
    (if (null? names)
        (reverse acc)
        (loop (cdr names) (+ i 1) (cons (list (car names) (ref i)) acc)))))

(define (record-properties object)
  (let* ((rtd (record-rtd object))
         (names (record-type-field-names rtd)))
    (append
      (list (list 'record-rtd rtd))
      (record-field-properties names (lambda (i) (%record-ref object i))))))

(define (rtd-properties rtd)
  (list (list 'rtd-name (record-type-name rtd))
        (list 'rtd-field-names (record-type-field-names rtd))))

;;; ---- Error / exception ----

(define (error-object-properties object)
  (list (list 'error-object-message (error-object-message object))
        (list 'error-object-irritants (error-object-irritants object))))

;;; ---- Hash table (srfi 69) ----

(define (hash-properties object)
  (append
    (list (list 'hash-table-size (hash-table-size object)))
    (map (lambda (kv) (list (car kv) (cdr kv))) (hash-table->alist object))))

;;; ---- Box (srfi 111) ----

(define (box-properties object)
  (list (list 'unbox (unbox object))))

;;; ---- Set / bag (srfi 113) ----

(define (set-properties object)
  (append
    (list (list 'set-size (set-size object)))
    (map (lambda (e) (list e e)) (set->list object))))

;; The SRFI's own suggested shape is a single bag->set entry, delegating
;; everything else to set-properties -- but curry's (srfi 113) has no
;; bag->set conversion. Reports bag-specific sizes and element->count
;; pairs directly instead (bag->alist already gives (element . count)).
(define (bag-properties object)
  (append
    (list (list 'bag-size (bag-size object))
          (list 'bag-unique-size (bag-unique-size object)))
    (map (lambda (kv) (list (car kv) (cdr kv))) (bag->alist object))))

;;; ---- Dispatch ----
;;;
;;; bag? must be checked before hash-table? -- (srfi 113)'s bags are
;;; hash tables under the hood (bag? is literally (and (hash-table? obj)
;;; ...)), so a bag would otherwise get the generic hash-table property
;;; set instead of its own.

(define (inspect-properties object)
  (append
    (object-properties object)
    (cond
      ((number? object)  (number-properties object))
      ((boolean? object) (boolean-properties object))
      ((box? object)     (box-properties object))
      ((bag? object)     (bag-properties object))
      ((hash-table? object) (hash-properties object))
      ((set? object)     (set-properties object))
      ((pair? object)    (pair-properties object))
      ((symbol? object)  (symbol-properties object))
      ((char? object)    (char-properties object))
      ((string? object)  (string-properties object))
      ((vector? object)  (vector-properties object))
      ((bytevector? object) (bytevector-properties object))
      ((error-object? object) (error-object-properties object))
      ((record-type? object) (rtd-properties object))
      ((record? object)  (record-properties object))
      (else '()))))

;;; inspect-describe

(define (assoc-ref key alist)
  (let ((entry (assoc key alist)))
    (if entry (cadr entry) #f)))

(define (inspect-describe object . port-arg)
  (let ((port (if (null? port-arg) (current-output-port) (car port-arg))))
    (cond
      ((number? object)
       (display "Number " port) (write object port) (newline port))
      ((boolean? object)
       (display "Boolean " port) (write object port) (newline port))
      ((box? object)
       (display "Box " port) (write (unbox object) port) (newline port))
      ((bag? object)
       (let ((props (inspect-properties object)))
         (display "Bag [" port) (display (assoc-ref 'bag-unique-size props) port)
         (display " unique, " port) (display (assoc-ref 'bag-size props) port)
         (display " total]" port) (newline port)))
      ((hash-table? object)
       (display "Hash table [" port) (display (hash-table-size object) port)
       (display "]" port) (newline port)
       (for-each (lambda (kv)
                   (display "  " port) (write (car kv) port)
                   (display " -> " port) (write (cdr kv) port) (newline port))
                 (hash-table->alist object)))
      ((set? object)
       (display "Set [" port) (display (set-size object) port) (display "]" port)
       (write (set->list object) port) (newline port))
      ((pair? object)
       (display "Pair " port) (write object port) (newline port))
      ((symbol? object)
       (display "Symbol " port) (display object port) (newline port))
      ((char? object)
       (display "Char " port) (write object port)
       (display " U+" port) (display (number->string (char->integer object) 16) port)
       (newline port))
      ((string? object)
       (display "String " port) (write object port)
       (display " (" port) (display (string-length object) port)
       (display " chars)" port) (newline port))
      ((vector? object)
       (display "Vector " port) (write object port) (newline port))
      ((bytevector? object)
       (display "Bytevector " port) (write object port) (newline port))
      ((error-object? object)
       (display "Error object " port) (write (error-object-message object) port)
       (display " " port) (write (error-object-irritants object) port) (newline port))
      ((record-type? object)
       (display "Record type " port) (display (record-type-name object) port)
       (display " " port) (write (record-type-field-names object) port) (newline port))
      ((record? object)
       (display "Record " port) (display (record-type-name (record-rtd object)) port)
       (display " " port) (write object port) (newline port))
      (else (write object port) (newline port)))))
