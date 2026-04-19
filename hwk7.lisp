#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 7.
 Due: 4/18 (Midnight)

 For this assignment, work in groups of 1-3. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 7".

 The group members are:

 Mingqi Lu

 To make sure that we are all on the same page, build the latest
 version of ACL2s, as per HWK1. You are going to be using SBCL, which
 you already have, due to the build process in

 Next, install quicklisp. See https://www.quicklisp.org/beta/. 

 To make sure everything is OK with quicklisp and to initialize it,
 start sbcl and issue the following commands

 (load "~/quicklisp/setup.lisp")
 (ql:quickload :trivia)
 (ql:quickload :cl-ppcre)
 (ql:quickload :let-plus)
 (setf ppcre:*allow-named-registers* t)
 (exit) 

 Next, clone the ACL2s interface repository:
 (https) https://gitlab.com/acl2s/external-tool-support/interface.git
 (ssh)   git@gitlab.com:acl2s/external-tool-support/interface.git

 This repository includes scripts for interfacing with ACL2s from lisp.
 Put this directory in the ...books/acl2s/ of your ACL2 repository, or 
 use a symbolic link.

 Now, certify the books, by going to ...books/acl2s/interface and
 typing 

 "cert.pl -j 4 top"

 Look at the documentation for cert.pl. If cert.pl isn't in your path,
 then use

 "...books/build/cert.pl -j 4 top"

 The "-j 4" option indicates that you want to run up to 4 instances of
 ACL2 in parallel. Set this number to the number of cores you have.

 As mentioned at the beginning of the semester, some of the code we
 will write is in Lisp. You can find the common lisp manual online in
 various formats by searching for "common lisp manual."

 Other references that you might find useful and are available online
 include
 
 - Common Lisp: A Gentle Introduction to Symbolic Computation by David
   Touretzky
 - ANSI Common Lisp by Paul Graham
 
|#

(in-package "ACL2S")

;; Now for some ACL2s systems programming.

;; This book is already included in ACL2s, so this is a no-op, but I'm
;; putting it here so that you can see where the code for ACL2s
;; systems programming is coming from.
(include-book "acl2s/interface/top" :dir :system)
(set-ignore-ok t)

;; This gets us to raw lisp.
:q

#| 

 The interface books provide us with the ability to call the theorem
 prover within lisp, which will be useful in checking your code. 

 Here are some examples you can try. 

 acl2s-compute is the form you use when you are using ACL2s to compute
 something, e.g., running a function on some input. 

 (acl2s-compute '(+ 1 2))

 acl2s-query is the form you use when you are querying ACL2s, e.g., a
 property without a name. If the property has a name, then that is not
 a query, but an event and you have to use acl2s-event.

 (acl2s-query 'acl2s::(property (p q :all)
                        (iff (=> p q)
                             (v (! p) q))))

 acl2s-arity is a function that determines if f is a function defined
 in ACL2s and if so, its arity (number of arguments). If f is not a
 function, then the arity is nil. Otherwise, the arity is a natural
 number. Note that f can't be a macro.

 (acl2s-arity 'acl2s::app)     ; is nil since app is a macro
 (acl2s-arity 'acl2s::bin-app) ; is 2

|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. Links to online documentation
 for the software libraries are provided below.

|#

(load "~/quicklisp/setup.lisp")

; See https://lispcookbook.github.io/cl-cookbook/pattern_matching.html
(ql:quickload :trivia)

; See https://www.quicklisp.org/beta/UNOFFICIAL/docs/cl-ppcre/doc/index.html
(ql:quickload :cl-ppcre)

; See https://github.com/sharplispers/let-plus
(ql:quickload :let-plus)

(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-compute and acl2s-query into our package.

(import 'acl2s::(acl2s-compute acl2s-query))
(import 'acl2s-interface-extras::(acl2s-arity))


#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t  )
    (not     :arity 1 :identity -   :idem nil :sink -  )
    (implies :arity 2 :identity -   :idem nil :sink -  )
    (iff     :arity - :identity t   :idem nil :sink -  )
    (if      :arity 3 :identity -   :idem nil :sink -  )))

#|

 mapcar is like map. See the common lisp manual.
 In general if you have questions about lisp, ask on Piazza.

|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2s formulas.

|#

(defun to-acl2s (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2S"))
    ((list 'iff) t)
    ((list 'iff p) (to-acl2s p))
    ((list* 'iff args)
     (acl2s::xxxjoin 'acl2s::iff
                     (mapcar #'to-acl2s args)))
    ((cons x xs)
     (mapcar #'to-acl2s f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean/non-keyword symbol. The arity
 of f is n and every occurrence of (f ...)  in a term or formula has
 to have arity n. Also, if f is a defined function in ACL2s, its arity
 has to match what ACL2s expects. We allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1 :junk-allowed t)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2s f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
           (mv-and res
                   (fo-termsp (cdr terms) fsig rsig)))))

#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure that you do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2s::acl2s-arity (to-acl2s r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))

(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
           (mv-and res
                   (fo-formulasp (cdr fs) fsig rsig)))))

#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
    (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 4. For example, you already implemented most of the
 simplifications in Question 1 in homework 4.
 
|#


#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

 A formula of the form (op ...) where op is a Boolean operator of
 arbitrary arity (ie, and, or, iff) applied to 0 or 1 arguments is not
 flat. For example, replace (and) with t.

 A formula of the form (op ... (op ...)) where op is a Boolean
 operator of arbitrary arity is not flat. For example, replace (and p
 q (and r s)) with (and p q r s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t 
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2s. For example, consider

 (acl2s-compute (to-acl2s '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2s '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.

 Make sure that your algorithm is as efficient as you can make
 it. The idea is to use this simplification as a preprocessing step,
 so it needs to be fast. 

 You are not required to perform any other simplifications beyond
 those specified above. If you do, your simplifier must be guaranteed
 to always return something that is simpler that what would be
 returned if you just implemented the simplifications explicitly
 requested. Also, if you implement any other simplifications, your
 algorithm must run in comparable time (eg, no validity checking).
 Notice some simple consequences. You cannot transform the formula to
 an equivalent formula that uses a small subset of the
 connectives (such as not/and). If you do that, the formula you get
 can be exponentially larger than the input formula, as we have
 discussed in class. Notice that even negation normal form (NNF) can
 increase the size of a formula. 

|#

(defun q1-union (a b)
  (remove-dups (append a b)))

(defun q1-difference (a b)
  (remove-if (lambda (x) (in x b)) a))

(defun q1-vars-list (vars)
  (if (consp vars) vars (list vars)))

(defun q1-free-vars-term (term)
  (cond
   ((variable-symbolp term) (list term))
   ((or (constant-symbolp term)
        (quotep term)
        (constant-objectp term)) nil)
   ((consp term)
    (reduce #'q1-union
            (mapcar #'q1-free-vars-term (cdr term))
            :initial-value nil))
   (t nil)))

(defun q1-free-vars-terms (terms)
  (reduce #'q1-union
          (mapcar #'q1-free-vars-term terms)
          :initial-value nil))

(defun q1-free-vars-formula (f)
  (cond
   ((booleanp f) nil)
   ((and (consp f) (== (car f) '=))
    (q1-free-vars-terms (cdr f)))
   ((and (consp f) (p-funp (car f)))
    (reduce #'q1-union
            (mapcar #'q1-free-vars-formula (cdr f))
            :initial-value nil))
   ((and (consp f) (in (car f) *fo-quantifiers*))
    (q1-difference (q1-free-vars-formula (third f))
                   (q1-vars-list (second f))))
   ((consp f)
    (q1-free-vars-terms (cdr f)))
   (t nil)))

(defun q1-quoted-or-constant-objectp (x)
  (or (quotep x)
      (constant-objectp x)))

(defun q1-try-acl2s-compute (term)
  (handler-case
      (let ((res (acl2s-compute (to-acl2s term) :quiet t)))
        (if (and (consp res) (not (car res)))
            (values t (second res))
          (values nil term)))
    (error () (values nil term))))

(defun q1-simplify-term (term)
  (cond
   ((or (constant-symbolp term)
        (variable-symbolp term)
        (quotep term)
        (constant-objectp term)) term)
   ((consp term)
    (let* ((f (car term))
           (args (mapcar #'q1-simplify-term (cdr term)))
           (new-term (cons f args)))
      (if (and (function-symbolp f)
               (every #'q1-quoted-or-constant-objectp args))
          (multiple-value-bind (ok val)
              (q1-try-acl2s-compute new-term)
            (if ok val new-term))
        new-term)))
   (t term)))

(defun q1-complementp (a b)
  (or (and (consp a)
           (== (car a) 'not)
           (== (len a) 2)
           (== (second a) b))
      (and (consp b)
           (== (car b) 'not)
           (== (len b) 2)
           (== (second b) a))))

(defun q1-remove-and-or-dups (args)
  (remove-dups args))

(defun q1-has-complements-p (args)
  (some (lambda (a)
          (some (lambda (b)
                  (q1-complementp a b))
                args))
        args))

(defun q1-flatten-same-op (op args)
  (mapcan (lambda (a)
            (if (and (consp a)
                     (== (car a) op))
                (copy-list (cdr a))
              (list a)))
          args))

(defun q1-make-and (args)
  (let* ((args (q1-flatten-same-op 'and args)))
    (cond
     ((in nil args) nil)
     (t
      (let ((args (q1-remove-and-or-dups (remove t args :test #'equal))))
        (cond
         ((q1-has-complements-p args) nil)
         ((endp args) t)
         ((endp (cdr args)) (car args))
         (t (cons 'and args))))))))

(defun q1-make-or (args)
  (let* ((args (q1-flatten-same-op 'or args)))
    (cond
     ((in t args) t)
     (t
      (let ((args (q1-remove-and-or-dups (remove nil args :test #'equal))))
        (cond
         ((q1-has-complements-p args) t)
         ((endp args) nil)
         ((endp (cdr args)) (car args))
         (t (cons 'or args))))))))

(defun q1-iff-arg-core (arg)
  (if (and (consp arg)
           (== (car arg) 'not)
           (== (len arg) 2))
      (values (second arg) t)
    (values arg nil)))

(defun q1-add-iff-core (core cores)
  (if (in core cores)
      (remove core cores :test #'equal :count 1)
    (cons core cores)))

(defun q1-make-not (arg)
  (cond
   ((booleanp arg) (not arg))
   ((and (consp arg)
         (== (car arg) 'not)
         (== (len arg) 2))
    (second arg))
   (t (list 'not arg))))

(defun q1-make-iff (args)
  (let ((args (q1-flatten-same-op 'iff args))
        (cores nil)
        (neg nil))
    (dolist (arg args)
      (cond
       ((== arg t))
       ((== arg nil) (setf neg (not neg)))
       (t
        (multiple-value-bind (core flipped)
            (q1-iff-arg-core arg)
          (when flipped
            (setf neg (not neg)))
          (setf cores (q1-add-iff-core core cores))))))
    (let ((base
           (cond
            ((endp cores) t)
            ((endp (cdr cores)) (car cores))
            (t (cons 'iff (nreverse cores))))))
      (if neg
          (q1-make-not base)
        base))))

(defun q1-simplify-atomic (f)
  (cond
   ((and (consp f) (== (car f) '=) (== (len f) 3))
    (list '= (q1-simplify-term (second f))
          (q1-simplify-term (third f))))
   ((consp f)
    (cons (car f) (mapcar #'q1-simplify-term (cdr f))))
   (t f)))

(defun q1-simplify-quantifier (q vars body)
  (let* ((simple-body (q1-simplify-formula body))
         (vars-list (q1-vars-list vars))
         (free-vars (q1-free-vars-formula simple-body))
         (kept-vars (remove-if-not (lambda (v) (in v free-vars)) vars-list)))
    (cond
     ((endp kept-vars) simple-body)
     ((consp vars) (list q kept-vars simple-body))
     (t (list q (car kept-vars) simple-body)))))

(defun q1-simplify-p-formula (op args)
  (let ((args (mapcar #'q1-simplify-formula args)))
    (case op
      (not
       (q1-make-not (car args)))
      (and
       (q1-make-and args))
      (or
       (q1-make-or args))
      (iff
       (q1-make-iff args))
      (implies
       (let ((a (first args))
             (b (second args)))
         (cond
          ((== a nil) t)
          ((== a t) b)
          ((== b t) t)
          ((== b nil) (q1-simplify-formula (list 'not a)))
          (t (list 'implies a b)))))
      (if
       (let ((c (first args))
             (a (second args))
             (b (third args)))
         (cond
          ((== c t) a)
          ((== c nil) b)
          ((== a b) a)
          ((and (== a t) (== b nil)) c)
          ((and (== a nil) (== b t)) (q1-simplify-formula (list 'not c)))
          ((== a t) (q1-simplify-formula (list 'or c b)))
          ((== a nil) (q1-simplify-formula (list 'and (list 'not c) b)))
          ((== b t) (q1-simplify-formula (list 'or (list 'not c) a)))
          ((== b nil) (q1-simplify-formula (list 'and c a)))
          (t (list 'if c a b)))))
      (otherwise
       (cons op args)))))

(defun q1-simplify-formula (f)
  (cond
   ((booleanp f) f)
   ((and (consp f) (p-funp (car f)))
    (q1-simplify-p-formula (car f) (cdr f)))
   ((and (consp f) (in (car f) *fo-quantifiers*) (== (len f) 3))
    (q1-simplify-quantifier (car f) (second f) (third f)))
   (t (q1-simplify-atomic f))))

(defun fo-simplify (f)
  (q1-simplify-formula f))

(defparameter *q1-tests*
  '(((and (p x) t (q t y) (q y z)) . (and (p x) (q t y) (q y z)))
    ((and (p x) t (q t b) nil) . nil)
    ((and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) . (and (p c) (= c '1) (r) (s) (or (r1) (r2))))
    ((and (p x) (not (p x)) (q y)) . nil)
    ((or (f) (f1) (p a b) (not (p a b)) (= w z)) . t)
    ((not (not (p x))) . (p x))
    ((forall (x w) (P y z)) . (P y z))
    ((forall (x w) (P x y z)) . (forall (x) (P x y z)))
    ((implies (p x) nil) . (not (p x)))
    ((if (p x) t (q x)) . (or (p x) (q x)))
    ((iff t (p x) nil) . (not (p x)))
    ((P (binary-+ 4 2) 3) . (P 6 3))))

(defun q1-run-tests ()
  (mapcar (lambda (test)
            (let ((res (fo-simplify (car test))))
              (list (car test) res (cdr test) (== res (cdr test)))))
          *q1-tests*))

#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

(defun q2-make-and (args)
  (q1-make-and args))

(defun q2-make-or (args)
  (q1-make-or args))

(defun q2-binary-iff-free (a b)
  (q2-make-and
   (list (q2-make-or (list (q2-nnf-neg a) b))
         (q2-make-or (list (q2-nnf-neg b) a)))))

(defun q2-iff-free (args)
  (cond
   ((endp args) t)
   ((endp (cdr args)) (car args))
   (t
    (q2-make-and
     (mapcar (lambda (x)
               (q2-binary-iff-free (car args) x))
             (cdr args))))))

(defun q2-nnf-pos (f)
  (cond
   ((booleanp f) f)
   ((and (consp f) (== (car f) 'not))
    (q2-nnf-neg (second f)))
   ((and (consp f) (== (car f) 'and))
    (q2-make-and (mapcar #'q2-nnf-pos (cdr f))))
   ((and (consp f) (== (car f) 'or))
    (q2-make-or (mapcar #'q2-nnf-pos (cdr f))))
   ((and (consp f) (== (car f) 'implies))
    (q2-make-or (list (q2-nnf-neg (second f))
                      (q2-nnf-pos (third f)))))
   ((and (consp f) (== (car f) 'iff))
    (q2-iff-free (mapcar #'q2-nnf-pos (cdr f))))
   ((and (consp f) (== (car f) 'if))
    (q2-make-or
     (list (q2-make-and (list (q2-nnf-pos (second f))
                              (q2-nnf-pos (third f))))
           (q2-make-and (list (q2-nnf-neg (second f))
                              (q2-nnf-pos (fourth f)))))))
   ((and (consp f) (== (car f) 'forall))
    (list 'forall (second f) (q2-nnf-pos (third f))))
   ((and (consp f) (== (car f) 'exists))
    (list 'exists (second f) (q2-nnf-pos (third f))))
   (t f)))

(defun q2-nnf-neg (f)
  (cond
   ((booleanp f) (not f))
   ((and (consp f) (== (car f) 'not))
    (q2-nnf-pos (second f)))
   ((and (consp f) (== (car f) 'and))
    (q2-make-or (mapcar #'q2-nnf-neg (cdr f))))
   ((and (consp f) (== (car f) 'or))
    (q2-make-and (mapcar #'q2-nnf-neg (cdr f))))
   ((and (consp f) (== (car f) 'implies))
    (q2-make-and (list (q2-nnf-pos (second f))
                       (q2-nnf-neg (third f)))))
   ((and (consp f) (== (car f) 'iff))
    (q2-nnf-neg (q2-iff-free (mapcar #'q2-nnf-pos (cdr f)))))
   ((and (consp f) (== (car f) 'if))
    (q2-nnf-neg
     (q2-make-or
      (list (q2-make-and (list (q2-nnf-pos (second f))
                               (q2-nnf-pos (third f))))
            (q2-make-and (list (q2-nnf-neg (second f))
                               (q2-nnf-pos (fourth f))))))))
   ((and (consp f) (== (car f) 'forall))
    (list 'exists (second f) (q2-nnf-neg (third f))))
   ((and (consp f) (== (car f) 'exists))
    (list 'forall (second f) (q2-nnf-neg (third f))))
   (t (q1-make-not f))))

(defun nnf (f)
  (fo-simplify (q2-nnf-pos (fo-simplify f))))

(defparameter *q2-tests*
  '(((implies (p x) (q x)) . (or (not (p x)) (q x)))
    ((not (implies (p x) (q x))) . (and (p x) (not (q x))))
    ((not (and (p x) (q x))) . (or (not (p x)) (not (q x))))
    ((not (or (p x) (q x))) . (and (not (p x)) (not (q x))))
    ((forall x (not (exists y (p x y)))) . (forall x (forall y (not (p x y)))))
    ((exists x (not (forall y (p x y)))) . (exists x (exists y (not (p x y)))))
    ((if (p x) (q x) (r x)) . (or (and (p x) (q x)) (and (not (p x)) (r x))))
    ((not (if (p x) (q x) (r x))) . (or (and (not (p x)) (not (r x))) (and (p x) (not (q x)))))
    ((iff (p x) (q x)) . (and (or (not (p x)) (q x)) (or (not (q x)) (p x))))
    ((not (not (p x))) . (p x))))

(defun q2-run-tests ()
  (mapcar (lambda (test)
            (let ((res (nnf (car test))))
              (list (car test) res (cdr test) (== res (cdr test)))))
          *q2-tests*))

#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 The fewer quantified variables, the better.
 The fewer Skolem functions, the better.
 The smaller the arity of Skolem functions, the better.
 Having said that, correctness should be your primary consideration.

 Test your functions using at least 10 interesting formulas. 
 
|#

(defun q3-fresh-var ()
  (gentemp "X"))

(defun q3-fresh-constant ()
  (gentemp "C"))

(defun q3-fresh-function ()
  (gentemp "F"))

(defun q3-lookup (x env)
  (cdr (assoc x env :test #'equal)))

(defun q3-subst-term (term subst)
  (cond
   ((variable-symbolp term)
    (let ((look (q3-lookup term subst)))
      (if look look term)))
   ((or (constant-symbolp term)
        (quotep term)
        (constant-objectp term)) term)
   ((consp term)
    (cons (car term)
          (mapcar (lambda (x) (q3-subst-term x subst)) (cdr term))))
   (t term)))

(defun q3-subst-formula (f subst)
  (cond
   ((booleanp f) f)
   ((and (consp f) (== (car f) '=))
    (list '= (q3-subst-term (second f) subst)
          (q3-subst-term (third f) subst)))
   ((and (consp f) (p-funp (car f)))
    (cons (car f)
          (mapcar (lambda (x) (q3-subst-formula x subst)) (cdr f))))
   ((and (consp f) (in (car f) *fo-quantifiers*))
    (list (car f) (second f)
          (q3-subst-formula
           (third f)
           (remove-if (lambda (p) (in (car p) (q1-vars-list (second f)))) subst))))
   ((consp f)
    (cons (car f)
          (mapcar (lambda (x) (q3-subst-term x subst)) (cdr f))))
   (t f)))

(defun q3-standardize-term (term env)
  (cond
   ((variable-symbolp term)
    (let ((look (q3-lookup term env)))
      (if look look term)))
   ((or (constant-symbolp term)
        (quotep term)
        (constant-objectp term)) term)
   ((consp term)
    (cons (car term)
          (mapcar (lambda (x) (q3-standardize-term x env)) (cdr term))))
   (t term)))

(defun q3-standardize-formula (f &optional (env nil))
  (cond
   ((booleanp f) f)
   ((and (consp f) (== (car f) '=))
    (list '= (q3-standardize-term (second f) env)
          (q3-standardize-term (third f) env)))
   ((and (consp f) (p-funp (car f)))
    (cons (car f)
          (mapcar (lambda (x) (q3-standardize-formula x env)) (cdr f))))
   ((and (consp f) (in (car f) *fo-quantifiers*))
    (let* ((vars (q1-vars-list (second f)))
           (new-vars (mapcar (lambda (x) (declare (ignore x)) (q3-fresh-var)) vars))
           (new-env (append (mapcar #'cons vars new-vars) env)))
      (list (car f)
            (if (consp (second f)) new-vars (car new-vars))
            (q3-standardize-formula (third f) new-env))))
   ((consp f)
    (cons (car f)
          (mapcar (lambda (x) (q3-standardize-term x env)) (cdr f))))
   (t f)))

(defun q3-skolem-term (universals)
  (if (endp universals)
      (q3-fresh-constant)
    (cons (q3-fresh-function) universals)))

(defun q3-skolemize (f &optional (universals nil))
  (cond
   ((booleanp f) f)
   ((and (consp f) (== (car f) 'forall))
    (let ((vars (q1-vars-list (second f))))
      (list 'forall (second f)
            (q3-skolemize (third f) (append universals vars)))))
   ((and (consp f) (== (car f) 'exists))
    (let* ((vars (q1-vars-list (second f)))
           (subst (mapcar (lambda (v) (cons v (q3-skolem-term universals))) vars)))
      (q3-skolemize (q3-subst-formula (third f) subst) universals)))
   ((and (consp f) (p-funp (car f)))
    (cons (car f) (mapcar (lambda (x) (q3-skolemize x universals)) (cdr f))))
   (t f)))

(defun q3-pull-forall (f)
  (cond
   ((and (consp f) (== (car f) 'forall))
    (multiple-value-bind (vars matrix)
        (q3-pull-forall (third f))
      (values (append (q1-vars-list (second f)) vars) matrix)))
   ((and (consp f) (p-funp (car f)))
    (let ((vars nil)
          (args nil))
      (dolist (arg (cdr f))
        (multiple-value-bind (v m)
            (q3-pull-forall arg)
          (setf vars (append vars v))
          (setf args (append args (list m)))))
      (values vars (cons (car f) args))))
   (t (values nil f))))

(defun q3-distribute-or (a b)
  (cond
   ((and (consp a) (== (car a) 'and))
    (q1-make-and
     (mapcar (lambda (x) (q3-distribute-or x b)) (cdr a))))
   ((and (consp b) (== (car b) 'and))
    (q1-make-and
     (mapcar (lambda (x) (q3-distribute-or a x)) (cdr b))))
   (t (q1-make-or (list a b)))))

(defun q3-cnf-matrix (f)
  (cond
   ((and (consp f) (== (car f) 'and))
    (q1-make-and (mapcar #'q3-cnf-matrix (cdr f))))
   ((and (consp f) (== (car f) 'or))
    (reduce #'q3-distribute-or
            (mapcar #'q3-cnf-matrix (cdr f))
            :initial-value nil))
   (t f)))

(defun q3-build-forall (vars matrix)
  (if (endp vars)
      matrix
    (list 'forall (remove-dups vars) matrix)))

(defun simp-skolem-pnf-cnf (f)
  (let* ((simple (fo-simplify f))
         (normal (nnf simple))
         (standard (q3-standardize-formula normal))
         (skolem (q3-skolemize standard)))
    (multiple-value-bind (vars matrix)
        (q3-pull-forall skolem)
      (fo-simplify (q3-build-forall vars (q3-cnf-matrix matrix))))))

(defun q3-no-exists-p (f)
  (cond
   ((atom f) t)
   ((and (consp f) (== (car f) 'exists)) nil)
   (t (every #'q3-no-exists-p f))))

(defun q3-cnf-p (f)
  (cond
   ((and (consp f) (== (car f) 'and))
    (every #'q3-cnf-clause-p (cdr f)))
   (t (q3-cnf-clause-p f))))

(defun q3-cnf-clause-p (f)
  (cond
   ((and (consp f) (== (car f) 'or))
    (every #'q3-literal-p (cdr f)))
   (t (q3-literal-p f))))

(defun q3-literal-p (f)
  (or (booleanp f)
      (and (consp f)
           (== (car f) 'not)
           (not (p-funp (car (second f)))))
      (and (consp f)
           (not (p-funp (car f)))
           (not (in (car f) *fo-quantifiers*)))))

(defun q3-result-p (f)
  (let ((res (simp-skolem-pnf-cnf f)))
    (and (q3-no-exists-p res)
         (if (and (consp res) (== (car res) 'forall))
             (q3-cnf-p (third res))
           (q3-cnf-p res)))))

(defparameter *q3-tests*
  '((exists x (p x))
    (forall x (exists y (p x y)))
    (or (p x) (and (q x) (r x)))
    (and (implies (p x) (q x)) (p x))
    (not (exists x (and (p x) (q x))))
    (forall x (or (p x) (exists y (q x y))))
    (exists (x y) (and (p x) (q y)))
    (if (p x) (q x) (r x))
    (iff (p x) (q x))
    (forall (x y) (exists z (or (not (p x)) (q y z))))))

(defun q3-run-tests ()
  (mapcar (lambda (test)
            (let ((res (simp-skolem-pnf-cnf test)))
              (list test res (q3-no-exists-p res)
                    (if (and (consp res) (== (car res) 'forall))
                        (q3-cnf-p (third res))
                      (q3-cnf-p res)))))
          *q3-tests*))


#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#

(defun q4-pair-left (p)
  (car p))

(defun q4-pair-right (p)
  (if (and (consp p) (consp (cdr p)) (null (cddr p)))
      (second p)
    (cdr p)))

(defun q4-compound-termp (x)
  (and (consp x) (not (quotep x))))

(defun q4-apply-term (term subst)
  (cond
   ((variable-symbolp term)
    (let ((look (q3-lookup term subst)))
      (if look (q4-apply-term look subst) term)))
   ((q4-compound-termp term)
    (cons (car term)
          (mapcar (lambda (x) (q4-apply-term x subst)) (cdr term))))
   (t term)))

(defun q4-occurs-p (v term subst)
  (let ((term (q4-apply-term term subst)))
    (cond
     ((== v term) t)
     ((q4-compound-termp term)
      (some (lambda (x) (q4-occurs-p v x subst)) (cdr term)))
     (t nil))))

(defun q4-extend-subst (v term subst)
  (let ((term (q4-apply-term term subst)))
    (if (q4-occurs-p v term subst)
        'fail
      (cons (cons v term)
            (mapcar (lambda (p)
                      (cons (car p) (q4-apply-term (cdr p) (list (cons v term)))))
                    subst)))))

(defun q4-unify-loop (pairs subst)
  (if (endp pairs)
      subst
    (let* ((p (car pairs))
           (s (q4-apply-term (q4-pair-left p) subst))
           (t1 (q4-apply-term (q4-pair-right p) subst)))
      (cond
       ((== s t1)
        (q4-unify-loop (cdr pairs) subst))
       ((variable-symbolp s)
        (let ((new-subst (q4-extend-subst s t1 subst)))
          (if (== new-subst 'fail)
              'fail
            (q4-unify-loop (cdr pairs) new-subst))))
       ((variable-symbolp t1)
        (let ((new-subst (q4-extend-subst t1 s subst)))
          (if (== new-subst 'fail)
              'fail
            (q4-unify-loop (cdr pairs) new-subst))))
       ((and (q4-compound-termp s)
             (q4-compound-termp t1)
             (== (car s) (car t1))
             (== (len s) (len t1)))
        (q4-unify-loop
         (append (mapcar #'cons (cdr s) (cdr t1)) (cdr pairs))
         subst))
       (t 'fail)))))

(defun unify (l)
  (q4-unify-loop l nil))

(defparameter *q4-tests*
  '((((x . c)) . ((x . c)))
    ((((f x) . (f c))) . ((x . c)))
    ((((f x y) . (f c d))) . ((y . d) (x . c)))
    ((((f x x) . (f c c))) . ((x . c)))
    ((((f x x) . (f c d))) . fail)
    ((x . (f x)) . fail)
    ((((f x) . (g x))) . fail)
    ((((p x c) . (p y y))) . ((y . c) (x . c)))
    ((((h x (g y)) . (h c (g d)))) . ((y . d) (x . c)))
    ((((f x y) . (f y c))) . ((y . c) (x . c)))))

(defun q4-test-input (x)
  (if (and (consp x) (consp (car x)) (consp (cdar x)))
      x
    (list x)))

(defun q4-run-tests ()
  (mapcar (lambda (test)
            (let ((res (unify (q4-test-input (car test)))))
              (list (car test) res (cdr test)
                    (or (== res (cdr test))
                        (and (!= res 'fail)
                             (!= (cdr test) 'fail)
                             (q4-subst-equivalent-p res (cdr test)))))))
          *q4-tests*))

(defun q4-subst-equivalent-p (a b)
  (and (every (lambda (p)
                (== (q4-apply-term (car p) a)
                    (q4-apply-term (car p) b)))
              a)
       (every (lambda (p)
                (== (q4-apply-term (car p) a)
                    (q4-apply-term (car p) b)))
              b)))

#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).


|#

(defun q5-matrix (f)
  (if (and (consp f) (== (car f) 'forall))
      (third f)
    f))

(defun q5-clause-lits (f)
  (cond
   ((== f t) nil)
   ((== f nil) (list nil))
   ((and (consp f) (== (car f) 'or)) (cdr f))
   (t (list f))))

(defun q5-cnf-clauses (f)
  (let ((m (q5-matrix f)))
    (cond
     ((== m t) nil)
     ((== m nil) (list nil))
     ((and (consp m) (== (car m) 'and))
      (mapcar #'q5-clause-lits (cdr m)))
     (t (list (q5-clause-lits m))))))

(defun q5-negative-literal-p (lit)
  (and (consp lit) (== (car lit) 'not) (== (len lit) 2)))

(defun q5-positive-part (lit)
  (if (q5-negative-literal-p lit) (second lit) lit))

(defun q5-complementary-p (a b)
  (or (and (q5-negative-literal-p a)
           (not (q5-negative-literal-p b))
           (== (car (second a)) (car b))
           (== (len (second a)) (len b)))
      (and (q5-negative-literal-p b)
           (not (q5-negative-literal-p a))
           (== (car a) (car (second b)))
           (== (len a) (len (second b))))))

(defun q5-lit-terms (lit)
  (cdr (q5-positive-part lit)))

(defun q5-unify-lits (a b)
  (if (q5-complementary-p a b)
      (unify (mapcar #'cons (q5-lit-terms a) (q5-lit-terms b)))
    'fail))

(defun q5-apply-lit (lit subst)
  (if (q5-negative-literal-p lit)
      (list 'not (q5-apply-lit (second lit) subst))
    (cons (car lit)
          (mapcar (lambda (x) (q4-apply-term x subst)) (cdr lit)))))

(defun q5-normalize-clause (clause)
  (let ((clause (remove-dups (remove nil clause :test #'equal))))
    (if (some (lambda (a)
                (some (lambda (b) (q1-complementp a b)) clause))
              clause)
        'tautology
      clause)))

(defun q5-apply-clause (clause subst)
  (q5-normalize-clause
   (mapcar (lambda (lit) (q5-apply-lit lit subst)) clause)))

(defun q5-clause-subsumes-p (a b)
  (some (lambda (sub)
          (and (!= sub 'fail)
               (let ((aa (q5-apply-clause a sub)))
                 (and (!= aa 'tautology)
                      (every (lambda (lit) (in lit b)) aa)))))
        (q5-subsumption-substs a b nil)))

(defun q5-subsumption-substs (a b subst)
  (if (endp a)
      (list subst)
    (mapcan
     (lambda (litb)
       (let* ((lita (q5-apply-lit (car a) subst))
              (litb (q5-apply-lit litb subst))
              (sub (q5-match-lit lita litb)))
         (if (== sub 'fail)
             nil
           (let ((merged (q5-merge-substs sub subst)))
             (if (== merged 'fail)
                 nil
               (q5-subsumption-substs (cdr a) b merged))))))
     b)))

(defun q5-match-lit (pattern target)
  (cond
   ((and (q5-negative-literal-p pattern)
         (q5-negative-literal-p target)
         (== (car (second pattern)) (car (second target)))
         (== (len (second pattern)) (len (second target))))
    (q5-match-terms (cdr (second pattern)) (cdr (second target)) nil))
   ((and (not (q5-negative-literal-p pattern))
         (not (q5-negative-literal-p target))
         (== (car pattern) (car target))
         (== (len pattern) (len target)))
    (q5-match-terms (cdr pattern) (cdr target) nil))
   (t 'fail)))

(defun q5-match-terms (patterns targets subst)
  (if (endp patterns)
      subst
    (let ((sub (q5-match-term (car patterns) (car targets) subst)))
      (if (== sub 'fail)
          'fail
        (q5-match-terms (cdr patterns) (cdr targets) sub)))))

(defun q5-match-term (pattern target subst)
  (let ((pattern (q4-apply-term pattern subst)))
    (cond
     ((variable-symbolp pattern)
      (let ((look (q3-lookup pattern subst)))
        (cond
         (look (if (== look target) subst 'fail))
         ((q4-occurs-p pattern target subst) 'fail)
         (t (cons (cons pattern target) subst)))))
     ((== pattern target) subst)
     ((and (q4-compound-termp pattern)
           (q4-compound-termp target)
           (== (car pattern) (car target))
           (== (len pattern) (len target)))
      (q5-match-terms (cdr pattern) (cdr target) subst))
     (t 'fail))))

(defun q5-merge-substs (a b)
  (let ((res b))
    (dolist (p a)
      (let ((new (unify (list (cons (q4-apply-term (car p) res)
                                    (q4-apply-term (cdr p) res))))))
        (if (== new 'fail)
            (return-from q5-merge-substs 'fail)
          (setf res (append new res)))))
    res))

(defun q5-replace-clauses (clauses new)
  (if (or (== new 'tautology)
          (some (lambda (old) (q5-clause-subsumes-p old new)) clauses))
      clauses
    (cons new
          (remove-if (lambda (old) (q5-clause-subsumes-p new old)) clauses))))

(defun q5-resolvent (c1 c2 l1 l2)
  (let ((sub (q5-unify-lits l1 l2)))
    (if (== sub 'fail)
        'fail
      (q5-apply-clause
       (append (remove l1 c1 :test #'equal :count 1)
               (remove l2 c2 :test #'equal :count 1))
       sub))))

(defun q5-all-resolvents (c1 c2)
  (let ((res nil))
    (dolist (l1 c1)
      (dolist (l2 c2)
        (let ((r (q5-resolvent c1 c2 l1 l2)))
          (when (!= r 'fail)
            (push r res)))))
    res))

(defun q5-resolution-loop (clauses &optional (limit 1000))
  (let ((clauses (reduce #'q5-replace-clauses
                         (mapcar #'q5-normalize-clause clauses)
                         :initial-value nil)))
    (loop for changed = nil
          for steps from 0 below limit
          do (let ((snapshot clauses))
               (dolist (c1 snapshot)
                 (dolist (c2 snapshot)
                   (dolist (r (q5-all-resolvents c1 c2))
                     (when (endp r)
                       (return-from q5-resolution-loop 'valid))
                     (let ((next (q5-replace-clauses clauses r)))
                       (when (!= next clauses)
                         (setf clauses next)
                         (setf changed t)))))))
             (unless changed
               (return clauses)))
    clauses))

(defun fo-no=-val (f)
  (let* ((neg (list 'not f))
         (cnf (simp-skolem-pnf-cnf neg))
         (clauses (q5-cnf-clauses cnf))
         (res (q5-resolution-loop clauses)))
    (if (== res 'valid) 'valid res)))

(defparameter *q5-tests*
  '((or (p c) (not (p c)))
    (implies (and (p c) (implies (p c) (q c))) (q c))
    (implies (forall x (implies (p x) (q x))) (implies (p c) (q c)))
    (implies (and (forall x (implies (p x) (q x))) (p c)) (q c))
    (implies (and (forall x (implies (human x) (mortal x))) (human c)) (mortal c))
    (implies (and (forall x (implies (p x) (r x))) (forall x (implies (r x) (q x))) (p c)) (q c))
    (implies (exists x (p x)) (exists y (p y)))
    (implies (forall x (p x)) (p c))
    (implies (p c) (exists x (p x)))
    (implies (and (or (p c) (q c)) (not (p c))) (q c))))

(defun q5-run-tests ()
  (mapcar (lambda (test)
            (list test (fo-no=-val test)))
          *q5-tests*))

#|

 Question 6. Extra Credit (20 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.

|#

(defun q6-eq-rel ()
  'equal-rel)

(defun q6-replace-equality (f)
  (cond
   ((booleanp f) f)
   ((and (consp f) (== (car f) '=))
    (cons (q6-eq-rel) (cdr f)))
   ((and (consp f) (p-funp (car f)))
    (cons (car f) (mapcar #'q6-replace-equality (cdr f))))
   ((and (consp f) (in (car f) *fo-quantifiers*))
    (list (car f) (second f) (q6-replace-equality (third f))))
   (t f)))

(defun q6-function-symbols-term (term)
  (cond
   ((q4-compound-termp term)
    (q1-union (list (cons (car term) (len (cdr term))))
              (reduce #'q1-union
                      (mapcar #'q6-function-symbols-term (cdr term))
                      :initial-value nil)))
   (t nil)))

(defun q6-symbols-formula (f)
  (cond
   ((booleanp f) (values nil nil))
   ((and (consp f) (p-funp (car f)))
    (let ((fs nil) (rs nil))
      (dolist (arg (cdr f))
        (multiple-value-bind (fsa rsa)
            (q6-symbols-formula arg)
          (setf fs (q1-union fs fsa))
          (setf rs (q1-union rs rsa))))
      (values fs rs)))
   ((and (consp f) (in (car f) *fo-quantifiers*))
    (q6-symbols-formula (third f)))
   ((consp f)
    (values (reduce #'q1-union
                    (mapcar #'q6-function-symbols-term (cdr f))
                    :initial-value nil)
            (list (cons (if (== (car f) '=) (q6-eq-rel) (car f))
                        (len (cdr f))))))
   (t (values nil nil))))

(defun q6-vars (n)
  (loop for i from 1 to n collect (intern (format nil "X~a" i) *package*)))

(defun q6-reflexive ()
  '(forall x (equal-rel x x)))

(defun q6-symmetric ()
  '(forall (x y) (implies (equal-rel x y) (equal-rel y x))))

(defun q6-transitive ()
  '(forall (x y z) (implies (and (equal-rel x y) (equal-rel y z)) (equal-rel x z))))

(defun q6-function-congruence (sig)
  (let* ((f (car sig))
         (n (cdr sig))
         (xs (q6-vars n))
         (ys (mapcar (lambda (x) (intern (format nil "Y~a" (subseq (symbol-name x) 1)) *package*)) xs))
         (hyps (mapcar (lambda (x y) (list (q6-eq-rel) x y)) xs ys)))
    (list 'forall (append xs ys)
          (list 'implies
                (if (endp hyps) t (cons 'and hyps))
                (list (q6-eq-rel) (cons f xs) (cons f ys))))))

(defun q6-relation-congruence (sig)
  (let* ((r (car sig))
         (n (cdr sig))
         (xs (q6-vars n))
         (ys (mapcar (lambda (x) (intern (format nil "Y~a" (subseq (symbol-name x) 1)) *package*)) xs))
         (hyps (mapcar (lambda (x y) (list (q6-eq-rel) x y)) xs ys)))
    (list 'forall (append xs ys)
          (list 'implies
                (cons 'and hyps)
                (list 'implies (cons r xs) (cons r ys))))))

(defun q6-equality-axioms (f)
  (multiple-value-bind (fs rs)
      (q6-symbols-formula f)
    (append (list (q6-reflexive) (q6-symmetric) (q6-transitive))
            (mapcar #'q6-function-congruence fs)
            (mapcar #'q6-relation-congruence
                    (remove (cons (q6-eq-rel) 2) rs :test #'equal)))))

(defun fo-val (f)
  (let* ((noeq (q6-replace-equality f))
         (axioms (q6-equality-axioms f))
         (full (list 'implies (cons 'and axioms) noeq)))
    (fo-no=-val full)))

(defparameter *q6-tests*
  '((= c c)
    (implies (= c d) (= d c))
    (implies (and (= c d) (= d e)) (= c e))
    (implies (= c d) (= (f c) (f d)))
    (implies (and (= c d) (p c)) (p d))
    (implies (and (= c d) (= d e) (p c)) (p e))
    (implies (and (= c d) (q (f c))) (q (f d)))
    (implies (and (= c d) (= e h)) (= (g c e) (g d h)))
    (implies (and (= c d) (r c e)) (r d e))
    (implies (and (= c d) (s (g c))) (s (g d)))))

(defun q6-run-tests ()
  (mapcar (lambda (test)
            (list test (fo-val test)))
          *q6-tests*))
