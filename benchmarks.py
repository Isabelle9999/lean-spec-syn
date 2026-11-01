from lean import LeanChecker

BENCHMARKS = [
    {
        "name": "insertionSort",
        "func_name": "insertionSort",
        "lean_code": """\
def insertSorted : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, h :: t => if x ≤ h then x :: h :: t else h :: insertSorted x t

def insertionSort : List Nat → List Nat
  | [] => []
  | h :: t => insertSorted h (insertionSort t)""",
        "test_inputs": ["[]", "[1]", "[3, 1, 2]", "[5, 2, 8, 1]"],
        "ground_truth": ["Perm", "Sorted", "length"],
        "templates": ["List Nat: List.Sorted, List.Perm, length"],
    },
    {
        "name": "mergeSort",
        "func_name": "mergeSort",
        "lean_code": """\
def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    let (l, r) := split t
    (x :: l, y :: r)

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

def mergeSortAux : Nat → List Nat → List Nat
  | 0, xs => xs
  | n + 1, [] => []
  | n + 1, [x] => [x]
  | n + 1, xs =>
    let (l, r) := split xs
    merge (mergeSortAux n l) (mergeSortAux n r)

def mergeSort (xs : List Nat) : List Nat := mergeSortAux xs.length xs""",
        "test_inputs": ["[]", "[1]", "[3, 1, 2]", "[5, 2, 8, 1]"],
        "ground_truth": ["Perm", "Sorted", "length"],
        "templates": ["List Nat: List.Sorted, List.Perm, length"],
    },
    {
        "name": "binarySearch",
        "func_name": "binarySearch",
        "lean_code": """\
def binarySearchAux (xs : Array Nat) (target lo hi : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if lo ≥ hi then none
    else
      let mid := lo + (hi - lo) / 2
      if xs[mid]! = target then some mid
      else if xs[mid]! < target then binarySearchAux xs target (mid + 1) hi fuel
      else binarySearchAux xs target lo mid fuel

def binarySearch (xs : Array Nat) (target lo hi : Nat) : Option Nat :=
  binarySearchAux xs target lo hi (hi - lo + 1)""",
        "test_inputs": ["#[1, 3, 5, 7, 9] 5 0 4", "#[1, 3, 5, 7, 9] 1 0 4", "#[2, 4, 6, 8] 6 0 3", "#[1, 2, 3] 4 0 2"],
        "ground_truth": ["some", "none", "< xs.size"],
        "templates": ["Array Nat, Option Nat: index bounds, membership, none when absent"],
    },
    {
        "name": "gcd",
        "func_name": "gcd'",
        "lean_code": """\
def gcd' (a b : Nat) : Nat :=
  if h : a = 0 then b else gcd' (b % a) a
termination_by a
decreasing_by
  apply Nat.mod_lt
  omega""",
        "test_inputs": ["0 5", "6 4", "12 8", "7 0"],
        "ground_truth": ["dvd", "= b", "gcd'"],
        "templates": ["Nat: divides, identity, commutativity"],
    },
    {
        "name": "bstInsert",
        "func_name": "bstInsert",
        "lean_code": """\
inductive BST where
  | leaf : BST
  | node : BST → Nat → BST → BST
  deriving Repr

def bstInsert (x : Nat) : BST → BST
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x < v then .node (bstInsert x l) v r
    else if x > v then .node l v (bstInsert x r)
    else .node l v r""",
        "test_inputs": [
            "5 BST.leaf",
            "3 (BST.node BST.leaf 5 BST.leaf)",
            "7 (BST.node BST.leaf 5 BST.leaf)",
        ],
        "ground_truth": ["member", "BST", "node"],
        "templates": ["BST: membership, structure preservation"],
    },
    {
        "name": "partition",
        "func_name": "partition",
        "lean_code": """\
def partition (p : Nat → Bool) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let (l, r) := partition p xs
    if p x then (x :: l, r) else (l, x :: r)""",
        "test_inputs": [
            "(· == 3) [1, 3, 2, 3]",
            "(· == 0) [0, 1, 0]",
            "(· == 5) [1, 2, 3]",
        ],
        "ground_truth": ["Perm", "= true", "= false"],
        "templates": ["List Nat × List Nat: permutation, predicate satisfaction"],
    },
    {
        "name": "listRange",
        "func_name": "range'",
        "lean_code": """\
def range' : Nat → List Nat
  | 0 => []
  | n + 1 => range' n ++ [n]""",
        "test_inputs": ["0", "1", "3", "5"],
        "ground_truth": ["length", "Sorted", "< n"],
    },
    {
        "name": "natPow",
        "func_name": "pow'",
        "lean_code": """\
def pow' : Nat → Nat → Nat
  | _, 0 => 1
  | a, n + 1 => a * pow' a n""",
        "test_inputs": ["2 0", "2 3", "3 2", "0 0"],
        "ground_truth": ["= 1", "pow' _ 1", "pow' 1"],
    },
]


if __name__ == "__main__":
    checker = LeanChecker()
    print("typechecking benchmarks...")
    for bm in BENCHMARKS:
        ok, errs = checker.typecheck(bm["lean_code"])
        if ok:
            print(f"  {bm['name']:20} ok")
        else:
            msg = errs[0][:80] if errs else "unknown error"
            print(f"  {bm['name']:20} FAIL: {msg}")
