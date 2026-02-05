'
Test 1: 5 + 10
AST for '5 + 10':
STATEMENT_LIST (1 statements):
  BINARY: +
    NUMBER: 5
    NUMBER: 10

Result: 15 (expected 15)
✓ PASS

Test 2: x = 5
AST for 'x = 5':
STATEMENT_LIST (1 statements):
  ASSIGNMENT: x (offset: -4)
    NUMBER: 5

Result: 5 (expected 5)
✓ PASS

Test 3: x = 5; x
AST for 'x = 5; x':
STATEMENT_LIST (2 statements):
  ASSIGNMENT: x (offset: -4)
    NUMBER: 5
  VARIABLE: x (offset: -4)

Result: 5 (expected 5)
✓ PASS

Test 4: x = 5; y = 10; x + y
AST for 'x = 5; y = 10; x + y':
STATEMENT_LIST (3 statements):
  ASSIGNMENT: x (offset: -4)
    NUMBER: 5
  ASSIGNMENT: y (offset: -8)
    NUMBER: 10
  BINARY: +
    VARIABLE: x (offset: -4)
    VARIABLE: y (offset: -8)

Result: 15 (expected 15)
✓ PASS

Test 5: x = 5; x * 2
AST for 'x = 5; x * 2':
STATEMENT_LIST (2 statements):
  ASSIGNMENT: x (offset: -4)
    NUMBER: 5
  BINARY: *
    VARIABLE: x (offset: -4)
    NUMBER: 2

Result: 10 (expected 10)
✓ PASS

Test 6: a = 10; b = 20; a + b * 2
AST for 'a = 10; b = 20; a + b * 2':
STATEMENT_LIST (3 statements):
  ASSIGNMENT: a (offset: -4)
    NUMBER: 10
  ASSIGNMENT: b (offset: -8)
    NUMBER: 20
  BINARY: +
    VARIABLE: a (offset: -4)
    BINARY: *
      VARIABLE: b (offset: -8)
      NUMBER: 2

Result: 50 (expected 50)
✓ PASS

Test 7: x = -5; x + 10
AST for 'x = -5; x + 10':
STATEMENT_LIST (2 statements):
  ASSIGNMENT: x (offset: -4)
    UNARY: -
      NUMBER: 5
  BINARY: +
    VARIABLE: x (offset: -4)
    NUMBER: 10

Result: 5 (expected 5)
✓ PASS

Test 8: x = 10; y = 3; x % y
AST for 'x = 10; y = 3; x % y':
STATEMENT_LIST (3 statements):
  ASSIGNMENT: x (offset: -4)
    NUMBER: 10
  ASSIGNMENT: y (offset: -8)
    NUMBER: 3
  BINARY: %
    VARIABLE: x (offset: -4)
    VARIABLE: y (offset: -8)

Result: 1 (expected 1)
✓ PASS

=== All tests complete ===
'
