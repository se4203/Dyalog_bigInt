# big.apl

Arbitrary-precision integer arithmetic for Dyalog APL.

All operations use a string-based interface: pass numbers as character vectors (e.g., `'123456789012345678901234567890'`) and get strings back. This lets you work with integers of any size, limited only by available workspace.

## Functions

### Arithmetic

| Function | Example | Result |
|----------|---------|--------|
| `a PLUS b` | `'999' big.PLUS '1'` | `'1000'` |
| `a MINUS b` | `'1000' big.MINUS '1'` | `'999'` |
| `a TIMES b` | `'123' big.TIMES '456'` | `'56088'` |
| `a DIVBY b` | `'123' big.DIVBY '56'` | `'2' '11'` |
| `a MOD b` | `'10' big.MOD '3'` | `'1'` |
| `a POWER b` | `'2' big.POWER '100'` | `'1267650600228229401496703205376'` |
| `NEGATE a` | `big.NEGATE '42'` | `'-42'` |
| `ABS a` | `big.ABS '-42'` | `'42'` |

`DIVBY` returns a two-element vector: quotient and remainder. `MOD` uses floored division, matching APL's `|` operator.

### Comparison

| Function | Example | Result |
|----------|---------|--------|
| `a CMP b` | `'100' big.CMP '99'` | `¯1` |
| `a GT b` | `'100' big.GT '99'` | `1` |
| `a LT b` | `'99' big.LT '100'` | `1` |
| `a GE b` | `'100' big.GE '100'` | `1` |
| `a LE b` | `'99' big.LE '100'` | `1` |
| `a MAX b` | `'5' big.MAX '10'` | `'10'` |
| `a MIN b` | `'5' big.MIN '10'` | `'5'` |

`CMP` returns `¯1` if the left argument is larger, `1` if the right is larger, and `0` if equal.

### Number Theory

| Function | Example | Result |
|----------|---------|--------|
| `a GCD b` | `'12' big.GCD '8'` | `'4'` |
| `a LCM b` | `'4' big.LCM '6'` | `'12'` |
| `base MODPOW exp mod` | `'4' big.MODPOW '13' '497'` | `'445'` |

### Combinatorics

| Function | Example | Result |
|----------|---------|--------|
| `FACTORIAL n` | `big.FACTORIAL '20'` | `'2432902008176640000'` |
| `k PERM n` | `'3' big.PERM '5'` | `'60'` |
| `k COMB n` | `'2' big.COMB '5'` | `'10'` |

`PERM` and `COMB` follow APL's convention where `k` is the left argument, matching `k!n`.

## Negative Numbers

Negative numbers are represented with a leading `'-'`, e.g., `'-123'`. All arithmetic and comparison functions handle negative arguments correctly.

## Multiplication Strategy

`TIMES` automatically selects between two algorithms depending on available workspace:

- **Outer product** for numbers that fit in memory (fast for small-to-medium inputs)
- **Karatsuba** divide-and-conquer for large numbers that would otherwise exhaust the workspace

## Division by Zero

`DIVBY` respects the `⎕DIV` system variable:

- `⎕DIV=0` (default): `'0' DIVBY '0'` returns `'1' '0'`; non-zero divided by zero signals `DOMAIN ERROR`
- `⎕DIV=1`: any `x DIVBY '0'` returns `'0' '0'`

## Tests

A built-in test suite is included as an inner namespace:

```apl
      big.Test.Run
84 of 84 tests passed
```

## Requirements

Dyalog APL (tested on version 16, Windows). The source file requires UTF-8 with BOM encoding.
