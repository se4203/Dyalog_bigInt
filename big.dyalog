:Namespace big
    ⎕io←0

    ∇ r←a PLUS b;aNeg;bNeg;isNeg;val
      (aNeg a)←u.stringToBig a
      (bNeg b)←u.stringToBig b
     
      :If ~aNeg∨bNeg    ⍝ both positive
          val←a u.add b
          isNeg←0
      :ElseIf aNeg∧bNeg ⍝ both negative
          val←a u.add b
          isNeg←1
      :Else             ⍝ different signs
          :Select aNeg,bNeg,a u.cmp b
          :Case 0 1 ¯1  ⍝ a pos ; b neg ; a>b
              val←a u.sub b
              isNeg←0
          :Case 0 1 1   ⍝ a pos ; b neg ; a<b
              val←b u.sub a
              isNeg←1
          :Case 1 0 ¯1  ⍝ a neg ; b pos ; a>b
              val←a u.sub b
              isNeg←1
          :Case 1 0 1   ⍝ a neg ; b pos ; a<b
              val←b u.sub a
              isNeg←0
          :CaseList (0 1 0)(1 0 0)  ⍝ a & b have different signs, but are equal
              val←,0
              isNeg←0
          :EndSelect
      :EndIf
     
      r←u.bigToString isNeg val
    ∇


    ∇ r←a MINUS b;bNeg
      (bNeg b)←u.stringToBig b
      r←a PLUS u.bigToString(~bNeg)b
    ∇


    ∇ r←a TIMES b;aNeg;bNeg;isNegative;val
      (aNeg a)←u.stringToBig a
      (bNeg b)←u.stringToBig b
      isNegative←aNeg≠bNeg
      :If (8×(≢a)×(≢a)+≢b)≤⎕WA
          val←a u.mul_outer b
      :Else
          val←a u.mul_karatsuba b
      :EndIf
      r←u.bigToString isNegative val
    ∇

    ∇ r←a DIVBY b;aNeg;bNeg;qNeg;rNeg;rem;qnt;trial;d
      (aNeg a)←u.stringToBig a
      (bNeg b)←u.stringToBig b
     
      ⍝ check if we're dividing by 0
      :If b≡,0
          :If ⎕DIV              ⍝ when this is true, x÷0 is 0 for all x
              r←(,'0')(,'0')
              :Return
          :ElseIf a≡,0          ⍝ otherwise it depends on the numerator
              r←(,'1')(,'0')    ⍝ 0÷0 is 1
              :Return
          :EndIf
          ⎕SIGNAL 11            ⍝ x÷0 is a domain error when x≠0
      :EndIf
     
      qNeg←aNeg≠bNeg            ⍝ is the quotient negative?
      rNeg←aNeg                 ⍝ is the remainder negative?
     
      :If a u.lt b
          r←(,'0')(u.bigToString rNeg a)
          :Return
      :EndIf
     
      rem←,0    ⍝ remainder
      qnt←⍬     ⍝ quotient
      :For d :In a
          rem←u.dl0 rem,d
          trial←9
          :While trial>0
              :If rem u.ge u.dl0⌽u.cry⌽trial×b
                  :Leave
              :EndIf
              trial-←1
          :EndWhile
          qnt,←trial
          :If trial>0   ⍝ no need to perform explicit subtraction when trial is 0
              rem←rem u.sub u.dl0⌽u.cry⌽trial×b
          :EndIf
      :EndFor
      qnt←u.dl0 qnt
      rNeg←rNeg∧~u.is0 rem          ⍝ suppress the negative sign if remainder is 0
      r←(u.bigToString qNeg qnt)(u.bigToString rNeg rem)
     
    ∇

    ∇ r←a MOD b
      r←1⊃a DIVBY b         ⍝ remainder from DIVBY
      :If ~u.is0 r            ⍝ if it's not zero ...
      :AndIf ≠/'-'=⊃¨a b    ⍝ ... and a & b have different signs ...
          r←r PLUS b        ⍝ ... then add to match APL's floored division
      :EndIf
    ∇

    ∇ r←a GCD b
      (a b)←u.abs¨a b
      :While ~u.is0 b
          (a b)←b(a MOD b)  ⍝ euclid's algo: replace larger value with remainder
      :EndWhile
      r←a
    ∇

    ∇ r←a LCM b
      :If u.is0 b
          r←,'0'
          :Return
      :EndIf
      r←⊃(u.abs a TIMES b)DIVBY(a GCD b)
    ∇

    ∇ r←base POWER exp
      ⎕SIGNAL('-'=⊃,exp)/11
      r←'1'
      :While ~u.is0 exp
          :If u.isOdd exp
              r←r TIMES base
          :EndIf
          exp←⊃exp DIVBY'2'
          base←base TIMES base
      :EndWhile
    ∇

    ∇ r←base MODPOW(exp mod)
      r←'1'
      base←base MOD mod
      :While ~u.is0 exp
          :If u.isOdd exp
              r←(r TIMES base)MOD mod
          :EndIf
          exp←⊃exp DIVBY'2'
          base←(base TIMES base)MOD mod
      :EndWhile
    ∇

    ∇ r←FACTORIAL n;nNeg;nVal
      (nNeg nVal)←u.stringToBig n
      ⎕SIGNAL nNeg/11
      :If nVal≡,0
          r←,1
      :Else
          r←⊃u.mul_outer/⌽(⎕D⍳⍕)¨1+⍳10⊥nVal
      :EndIf
      r←u.bigToString 0 r
    ∇

    ∇ r←k PERM n;nNeg;nVal;kNeg;kVal;num;i
      (nNeg nVal)←u.stringToBig n
      (kNeg kVal)←u.stringToBig k
      ⎕SIGNAL(nNeg∨kNeg)/11
      ⎕SIGNAL(nVal u.lt kVal)/11
     
      :If kVal≡,0
          r←,'1'
          :Return
      :EndIf
     
    ⍝ P(k,n) = n × (n-1) × ... × (n-k+1)
      num←,1
      i←,0
      :While i u.lt kVal
          num←num u.mul_outer(nVal u.sub i)
          i←i u.add,1
      :EndWhile
     
      r←u.bigToString 0 num
    ∇

    ∇ r←k COMB n;nNeg;nVal;kNeg;kVal;difference
      (nNeg nVal)←u.stringToBig n
      (kNeg kVal)←u.stringToBig k
      ⎕SIGNAL(nNeg∨kNeg)/11
      ⎕SIGNAL(nVal u.lt kVal)/11
     
     ⍝ symmetry: C(k,n) = C(n-k,n)
      :If kVal u.gt difference←(nVal u.sub kVal)
          k←u.bigToString 0 difference
      :EndIf
     
      r←⊃(k PERM n)DIVBY FACTORIAL k
    ∇

      NEGATE←{
          (isNeg value)←u.stringToBig ⍵
          sign←(value≢,0)∧~isNeg
          u.bigToString sign value
      }

    ABS←{u.bigToString 0(1⊃u.stringToBig ⍵)}

    ∇ r←a CMP b;aNeg;bNeg
      (aNeg a)←u.stringToBig a
      (bNeg b)←u.stringToBig b
      :If bNeg∧~aNeg       ⍝ a positive, b negative
          r←¯1
      :ElseIf aNeg∧~bNeg   ⍝ a negative, b positive
          r←1
      :ElseIf aNeg         ⍝ both negative: reverse the comparison
          r←b u.cmp a
      :Else                ⍝ both positive
          r←a u.cmp b
      :EndIf
    ∇

    GT←{¯1=⍺ CMP ⍵}
    LT←{1=⍺ CMP ⍵}
    GE←{1≠⍺ CMP ⍵}
    LE←{¯1≠⍺ CMP ⍵}
    MAX←{¯1=⍺ CMP ⍵:⍺ ⋄ ⍵}
    MIN←{1=⍺ CMP ⍵:⍺ ⋄ ⍵}

    :Namespace u
        ⎕io←0

        ∇ r←a add b
         
          (a b)←a pad b
          (a b)←⌽¨a b               ⍝ reverse both arrays
          r←dl0⌽cry a+b             ⍝ add terms element-wise and perform carry
        ∇

        ∇ r←cry sum;res;nxt
         
          :Repeat
              res←10|sum            ⍝ digit in this position
              nxt←⌊sum÷10           ⍝ carry to next position
              sum←(res,0)+(0,nxt)   ⍝ new sum
          :Until ∧/sum≤9            ⍝ keep carrying
         
          r←sum
        ∇

        ∇ r←a sub b;brw;dif;res
         
          (a b)←a pad b
          (a b)←⌽¨a b                ⍝ reverse both arrays
         
          dif←a-b
          :Repeat
              res←10|dif             ⍝ digit in this position
              brw←⌊(dif<0)÷¯10       ⍝ borrow
              dif←(res,0)+(0,brw)    ⍝ new difference
          :Until ∧/dif≥0             ⍝ keep borrowing
         
          r←dl0⌽dif
        ∇

        ∇ r←a mul_karatsuba b;m;ahi;alo;bhi;blo;p1;p2;p3;mid
          ⍝ base case: small enough for outer product
          :If 50≥⌈/≢¨a b
              r←a mul_outer b
              :Return
          :EndIf
          ⍝ split a and b at midpoint m: e.g. 12345 → hi=12 lo=345 when m=3
          m←⌊(⌈/≢¨a b)÷2
          :If m≥≢a
              ahi←,0 ⋄ alo←a
          :Else
              ahi←((≢a)-m)↑a ⋄ alo←(-m)↑a
          :EndIf
          :If m≥≢b
              bhi←,0 ⋄ blo←b
          :Else
              bhi←((≢b)-m)↑b ⋄ blo←(-m)↑b
          :EndIf
          ⍝ three half-size multiplications instead of one full-size
          p1←ahi mul_karatsuba bhi              ⍝ hi × hi
          p2←alo mul_karatsuba blo              ⍝ lo × lo
          p3←(ahi add alo)mul_karatsuba(bhi add blo)  ⍝ (hi+lo) × (hi+lo)
          mid←p3 sub(p1 add p2)                ⍝ cross term: hi×lo + lo×hi
          ⍝ combine with positional shifts (appending zeros = multiplying by 10∧m)
          r←(p1,((2×m)⍴0))add(mid,(m⍴0))add p2
        ∇

          mul_outer←{
              mx←⍺∘.×⍵              ⍝ outer product to make all pair-wise digit-products
              mx,←(0 ¯1+≢⍺)⍴0       ⍝ append columns of 0s
              ad←+⌿(-⍳≢⍺)⌽mx        ⍝ rotate to align the anti-diagonals as columns and add them
              dl0⌽cry⌽ad            ⍝ add them with carrying and remove leading 0s
          }

        abs←{⍵~'-'}

        is0←{⍵≡,'0'}
        isOdd←{2|⍎⊃⌽⍵}  ⍝ ⍵ is odd/even iff the last digit is odd/even

          cmp←{
          ⍝ returns ¯1 if ⍺ is larger
          ⍝          1 if ⍵ is larger
          ⍝          0 if equal
            ⍝ compare lengths
              r←×-/≢¨⍵ ⍺
              r≠0:r
              ×⊃0~⍨⍵-⍺
          }

          pad←{
              lenDiff←-/≢¨⍺ ⍵
              padding←(|lenDiff)/0
              lenDiff>0:⍺(padding,⍵)
              lenDiff<0:(padding,⍺)⍵
              ⍺ ⍵
          }

          stringToBig←{
              str←,⍵
              isNegative←'-'=⊃⍵
              str←isNegative↓str
              0=≢str:⎕SIGNAL 11
              ×≢str~⎕D:⎕SIGNAL 11
              isNegative,⊂⍎¨str
          }

          bigToString←{
              (isNegative digits)←⍵
              str←⎕D[digits]
              isNegative:'-',str
              str
          }

          dl0←{
              r←(∨\⍵≠0)/⍵   ⍝ r: ⍵ without leading 0s
              0=≢r:,0       ⍝ return single 0 if nothing left
              r
          }

        gt←{¯1=⍺ cmp ⍵} ⍝ ⍺ > ⍵
        lt←{1=⍺ cmp ⍵}  ⍝ ⍺ < ⍵
        ge←{1≠⍺ cmp ⍵}   ⍝ ⍺ ≥ ⍵
        le←{¯1≠⍺ cmp ⍵}  ⍝ ⍺ ≤ ⍵

    :EndNamespace

    :Namespace Test
        ∇ r←Run;passed;failed;total;results
          results←⍬
          results,←Arithmetic
          results,←Comparison
          results,←Division
          results,←Modular
          results,←Combinatorics
          results,←SignAndAbs
          results,←EdgeCases 
          results,←ErrorHandling
          passed←+/results
          total←≢results
          failed←total-passed
          r←(⍕passed),' of ',(⍕total),' tests passed'
          :If failed>0
              r,←' (',(⍕failed),' FAILED)'
          :EndIf
        ∇

        ∇ r←check(expected actual)
          r←(,expected)≡,actual
          :If ~r
              ⎕←'FAIL: expected ',(⍕expected),' got ',(⍕actual)
          :EndIf
        ∇

        ∇ r←checkDiv(expQ expR actual)
          r←(check(expQ(⊃actual)))∧check(expR(1⊃actual))
        ∇

        ∇ r←Arithmetic;t
          r←⍬
          r,←check'579'('123'##.PLUS'456')
          r,←check'1000'('999'##.PLUS'1')
          r,←check'0'('500'##.PLUS'-500')
          r,←check'-333'('-123'##.PLUS'-210')
          r,←check'100'('123'##.MINUS'23')
          r,←check'-100'('23'##.MINUS'123')
          r,←check'0'('123'##.MINUS'123')
          r,←check'56088'('123'##.TIMES'456')
          r,←check'-56088'('-123'##.TIMES'456')
          r,←check'56088'('-123'##.TIMES'-456')
          r,←check'0'('0'##.TIMES'999')
          r,←check'998001'('999'##.TIMES'999')
        ∇

        ∇ r←Comparison
          r←⍬
          r,←check(¯1)('456'##.CMP'123')
          r,←check 1('123'##.CMP'456')
          r,←check 0('123'##.CMP'123')
          r,←check(¯1)('5'##.CMP'-5')
          r,←check 1('-5'##.CMP'5')
          r,←check 0('-5'##.CMP'-5')
          r,←check 1('123'##.GT'100')
          r,←check 0('100'##.GT'123')
          r,←check 0('100'##.LT'100')
          r,←check 1('100'##.LT'123')
          r,←check 1('100'##.GE'100')
          r,←check 1('123'##.GE'100')
          r,←check 0('100'##.GE'123')
          r,←check 1('100'##.LE'100')
          r,←check 1('100'##.LE'123')
          r,←check 0('123'##.LE'100')
          r,←check'10'('10'##.MAX'5')
          r,←check'10'('5'##.MAX'10')
          r,←check'5'('5'##.MAX'5')
          r,←check'5'('10'##.MIN'5')
          r,←check'5'('5'##.MIN'10')
          r,←check'5'('5'##.MIN'5')
          r,←check'-5'('-5'##.MAX'-10')
          r,←check'-10'('-5'##.MIN'-10')
        ∇

        ∇ r←Division
          r←⍬
          r,←checkDiv'2' '11'('123'##.DIVBY'56')
          r,←checkDiv'0' '5'('5'##.DIVBY'10')
          r,←checkDiv'100' '0'('100'##.DIVBY'1')
          r,←checkDiv'-100' '0'('100'##.DIVBY'-1')
          r,←checkDiv'1' '0'('456'##.DIVBY'456')
        ∇

        ∇ r←Modular
          r←⍬
          r,←check'1'('10'##.MOD'3')
          r,←check'0'('10'##.MOD'5')
          r,←check'2'('10'##.GCD'6')
          r,←check'2'('10'##.GCD'6'##.GCD'8')
          r,←check'30'('10'##.LCM'6')
          r,←check'445'('4'##.MODPOW'13' '497')
        ∇

        ∇ r←Combinatorics
          r←⍬
          r,←check'120'(##.FACTORIAL'5')
          r,←check'1'(##.FACTORIAL'0')
          r,←check'3628800'(##.FACTORIAL'10')
          r,←check'10'('2'##.COMB'5')
          r,←check'1'('0'##.COMB'5')
          r,←check'1'('5'##.COMB'5')
          r,←check'60'('3'##.PERM'5')
          r,←check'1'('0'##.PERM'5')
          r,←check'120'('5'##.PERM'5')
          r,←check'1'('2'##.POWER'0')
          r,←check'1024'('2'##.POWER'10')
          r,←check'8'('2'##.POWER'3')
          r,←check'1'('1'##.POWER'100')
          r,←check'0'('0'##.POWER'5')
        ∇

        ∇ r←SignAndAbs
          r←⍬
          r,←check'-123'(##.NEGATE'123')
          r,←check'123'(##.NEGATE'-123')
          r,←check'0'(##.NEGATE'0')
          r,←check'123'(##.ABS'123')
          r,←check'123'(##.ABS'-123')
          r,←check'0'(##.ABS'0')
        ∇

     ∇ r←EdgeCases;⎕DIV
            r←⍬
            r,←check '0' ('0'##.PLUS'0')
            r,←check '0' ('0'##.TIMES'0')
            r,←check '1' ('1'##.TIMES'1')
            ⍝ ⎕DIV=0 (default): 0÷0 is 1
            ⎕DIV←0
            r,←checkDiv '1' '0' ('0'##.DIVBY'0')
            ⍝ ⎕DIV=1: x÷0 is 0 for all x
            ⎕DIV←1
            r,←checkDiv '0' '0' ('0'##.DIVBY'0')
            r,←checkDiv '0' '0' ('1'##.DIVBY'0')
            r,←checkDiv '0' '0' ('123'##.DIVBY'0')
          ∇

        ∇ r←ErrorHandling;t
          r←⍬
            ⍝ invalid input: non-digit string
          t←0
          :Trap 11
              'abc'##.PLUS'123'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ invalid input: empty string
          t←0
          :Trap 11
              ''##.PLUS'123'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ division by zero
          t←0
          :Trap 11
              '1'##.DIVBY'0'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ negative factorial
          t←0
          :Trap 11
              ##.FACTORIAL'-1'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ negative exponent
          t←0
          :Trap 11
              '2'##.POWER'-3'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ PERM: k > n
          t←0
          :Trap 11
              '6'##.PERM'5'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ PERM: negative k
          t←0
          :Trap 11
              '-1'##.PERM'5'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ COMB: k > n
          t←0
          :Trap 11
              '6'##.COMB'5'
          :Else
              t←1
          :EndTrap
          r,←t
            ⍝ COMB: negative n
          t←0
          :Trap 11
              '2'##.COMB'-5'
          :Else
              t←1
          :EndTrap
          r,←t
        ∇

    :EndNamespace

:EndNamespace
