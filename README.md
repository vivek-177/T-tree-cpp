## T-Tree Implementation in C++

A complete implementation of the **T-Tree** data structure proposed by Lehman & Carey (VLDB 1986). The project supports insertion, deletion, and search while maintaining AVL balance and the occupancy constraints of T-Trees.

## Features

- AVL-balanced T-Tree
- Search
- Insertion
- Deletion
- GLB/GUB based rebalancing
- Parent pointer maintenance
- Invariant verification
- Regression tests
- Randomized fuzz testing

## Project Structure

```
src/
    ttree.cpp
```

## Build

```bash
make
```

or

```bash
g++ -std=c++17 -O2 src/ttree.cpp -o ttree
```

## Run Demo

```bash
./ttree
```

## Run Fuzz Tests

```bash
./ttree fuzz
```

## Time Complexity

| Operation | Complexity |
| --------- | ---------- |
| Search    | O(log n)   |
| Insert    | O(log n)   |
| Delete    | O(log n)   |

## Highlights

- Implements AVL rotations
- Maintains T-Tree occupancy rules
- Verifies structural invariants after every operation
- Includes randomized stress testing
- Includes targeted regression tests

## References

<<<<<<< HEAD
- Lehman, T. J., & Carey, M. J. (1986). _A Study of Index Structures for Main Memory Database Management Systems_. Proceedings of the 12th VLDB Conference.
=======
- Lehman, T. J., & Carey, M. J. (1986). *A Study of Index Structures for Main Memory Database Management Systems*. Proceedings of the 12th VLDB Conference.

- ...
>>>>>>> 29a406e57470900c2cc9ae75ac8cd9317fe1cfbe
