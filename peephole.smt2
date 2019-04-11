#if BITS==5
#define HIGHBIT  4
#define HIGHBIT2 3
#define ZERO #b00000
#define ONE  #b00001
#define NEGONE #b11111
#else
#define BITS 64
#define HIGHBIT  63
#define HIGHBIT2 62
#define ZERO #x0000000000000000
#define ONE  #x0000000000000001
#define NEGONE #x1111111111111111
#endif

(define-sort ocaml-int () (_ BitVec BITS))

(declare-datatypes () ((CMP EQ NE LT GT LE GE)))

(declare-datatypes () ((ILOG AND OR XOR)))

(define-fun ocaml-lsl ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvshl x y))

(define-fun ocaml-lsr ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvlshr x y))

(define-fun ocaml-or ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvor x y))

(define-fun ocaml-and ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvand x y))

(define-fun ocaml-xor ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvxor x y))

(define-fun ocaml-has-tag ((x ocaml-int)) bool
  (= (ocaml-and x ONE) ONE))

(define-fun ocaml-highest-bits-same ((x ocaml-int)) bool
  (= ((_ extract HIGHBIT HIGHBIT) x) ((_ extract HIGHBIT2 HIGHBIT2) x)))

(define-fun ocaml-asr-1 ((x ocaml-int)) ocaml-int
  (concat
    ((_ extract HIGHBIT HIGHBIT) x)
    ((_ extract HIGHBIT2 0) (ocaml-lsr x ONE))
    ))

(define-fun ocaml-lsr-1 ((x ocaml-int)) ocaml-int
  (ocaml-lsr x ONE))

(define-fun ocaml-addi ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvadd x y))

(define-fun ocaml-subi ((x ocaml-int) (y ocaml-int)) ocaml-int
  (bvsub x y))

(define-fun ocaml-tagi ((x ocaml-int)) ocaml-int
  (bvadd (ocaml-lsl x ONE) ONE))

(define-fun ocaml-untagi ((x ocaml-int)) ocaml-int
  (ocaml-asr-1 x))

(define-fun ocaml-to-int-untagged ((x ocaml-int)) Int
  (+ (if (= ((_ extract HIGHBIT HIGHBIT) x) #b1) -16 0)
  (bv2int ((_ extract HIGHBIT2 0) x))))

(define-fun ocaml-cmp-eq ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (= x y) ONE ZERO))

(define-fun ocaml-cmp-ne ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (not (= x y)) ONE ZERO))

(define-fun ocaml-cmp-lt ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (bvslt x y)
    ONE ZERO))

(define-fun ocaml-cmp-gt ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (bvsgt x y)
    ONE ZERO))

(define-fun ocaml-cmp-le ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (bvsle x y)
    ONE ZERO))

(define-fun ocaml-cmp-ge ((x ocaml-int) (y ocaml-int)) ocaml-int
  (if (bvsge x y)
    ONE ZERO))

(define-fun ocaml-cmp ((cmp CMP) (x ocaml-int) (y ocaml-int)) ocaml-int
  (match cmp
    (case EQ (ocaml-cmp-eq x y))
    (case NE (ocaml-cmp-ne x y))
    (case LT (ocaml-cmp-lt x y))
    (case GT (ocaml-cmp-gt x y))
    (case LE (ocaml-cmp-le x y))
    (case GE (ocaml-cmp-ge x y))
    ))

(define-fun ocaml-ilog ((ilog ILOG) (x ocaml-int) (y ocaml-int)) ocaml-int
  (match ilog
    (case AND (ocaml-and x y))
    (case OR  (ocaml-or x y))
    (case XOR (ocaml-xor x y))
  ))

;| Cop(Ccmpi cmpop
;￼	       , [ Cop(Caddi,[Cop(Clsl,[left;Cconst_int(1,_)],_);Cconst_int(1,_)],_)
;￼	         ; Cconst_int (right_i,right_dbg)
;￼	         ]
;￼	       , dbg_cmp
;￼	       ) ->
;￼	      Cop (Ccmpi cmpop, [ left; Cconst_int (right_i asr 1, right_dbg)], dbg_cmp)

(declare-const left ocaml-int)
(declare-const right ocaml-int)
(declare-const cmpop CMP)

(push 1)
(echo "Checking 1")

(assert (not (=
  (ocaml-cmp-eq (ocaml-tagi left) right)
  (ocaml-cmp-eq left (ocaml-asr-1 right))
  )))

(assert (ocaml-has-tag right))
(assert (ocaml-highest-bits-same left))
(check-sat)
(get-model)
(pop 1)
;------------------------------

(push 1)
(echo "Checking 2")

(assert (not (=
  (ocaml-cmp cmpop (ocaml-tagi left) right)
  (ocaml-cmp cmpop (ocaml-lsl left ONE) (ocaml-subi right ONE))
  )))

(assert (ocaml-has-tag right))

(check-sat)
(get-model)
(pop 1)
;------------------------------

(push 1)
(echo "Checking 3")

(declare-const ilog-op ILOG)

(assert (or (= ilog-op AND) (= ilog-op OR)))

(assert (not (=
  (ocaml-ilog ilog-op (ocaml-tagi left) (ocaml-tagi right))
  (ocaml-tagi (ocaml-ilog ilog-op left right))
)))

(check-sat)
(get-model)
(pop 1)
;------------------------------
(push 1)
(echo "Checking 4")

(assert (not (=
  (ocaml-ilog XOR (ocaml-tagi left) (ocaml-tagi right))
  (ocaml-tagi (ocaml-ilog XOR left right))
)))

(check-sat)
(get-model)
(pop 1)
;------------------------------

(push 1)
(echo "Checking 5")

(declare-const cmp-outer CMP)
(declare-const cmp-inner CMP)
(declare-const val-1 ocaml-int)
(declare-const val-2 ocaml-int)

; (!= (+ (<< (== val/1 val/2) 1) 1) 1)
; =>
; (!= (== val/1 val/2) 0)

(assert (not (=
  (ocaml-cmp cmp-outer (ocaml-tagi (ocaml-cmp cmp-inner val-1 val-2)) ONE)
  (ocaml-cmp cmp-outer (ocaml-cmp cmp-inner val-1 val-2) ZERO)
)))

(check-sat)
(get-model)
(pop 1)
;------------------------------
