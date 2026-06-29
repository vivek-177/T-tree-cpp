#include <bits/stdc++.h>
using namespace std;

/*
  T-Tree implementation following Lehman & Carey (1986),
  "A Study of Index Structures for Main Memory Database Management Systems"
  (12th VLDB Conference, pp. 294-303).

  This implements the algorithm's actual insert/delete discipline rather
  than a B-tree-style "split and promote" approximation. The structural
  rules below are taken from the paper as summarized in standard secondary
  references (e.g. the Wikipedia T-tree article, which mirrors the paper's
  algorithm closely) and cross-checked against the paper's design intent.

  ===========================================================================
  TERMINOLOGY
  ===========================================================================
  - leaf node:      no children.
  - half-leaf node: exactly one child, and that child is a leaf.
  - internal node:  two children.
  - bounding node for value v: the (unique) node whose [min,max] range
    contains v, inclusive.
  - GLB node (greatest-lower-bound node) of node N: found via N->left,
    then following ->right repeatedly. Holds the in-order predecessor key
    of N's minimum. The paper guarantees this node is always a leaf or
    half-leaf (never internal) -- an invariant this implementation
    actively checks rather than assumes.
  - GUB node (least-upper-bound node) of node N: symmetric, via N->right
    then ->left repeatedly. Always a leaf or half-leaf.

  ===========================================================================
  OCCUPANCY RULES
  ===========================================================================
  - MAX_KEYS: hard cap on every node's array size.
  - MIN_KEYS: applies ONLY to internal nodes. Per the paper: "Leaf and
    half-leaf nodes can contain any number of data elements from one to
    the maximum size of the data array" -- i.e. leaves/half-leaves are
    explicitly exempt from MIN_KEYS. Internal nodes must stay at >= MIN_KEYS,
    enforced by borrowing from the GLB node whenever a delete (or a
    rotation) would otherwise drop an internal node below that floor.

  ===========================================================================
  INSERT
  ===========================================================================
  1. Search for the bounding node of the new value.
  2. Bounding node B found:
       a. B has room          -> insert directly into B's array. Done.
       b. B is full           -> evict B's current MINIMUM key, insert the
                                  new key into B (sorted position), then:
            - let G = GLB node of B.
            - G exists and has room  -> append evicted as G's new max.
            - G exists and is full   -> create a NEW RIGHT CHILD of G
                                         holding just `evicted`.
            - G does not exist (B has no left subtree, so there's no
              predecessor node at all) -> create a NEW LEFT CHILD of B
              holding just `evicted` (nothing else can hold values below
              B's range in this case).
          This "borrow from predecessor before creating a new node" step
          is the defining T-tree behavior that a naive "split and spawn a
          node every time" implementation skips.
  3. No bounding node found (value falls in a gap below/above an existing
     leaf/half-leaf with no relevant child): let L be the last node
     visited during the search.
       a. L has room  -> insert the value into L directly (becomes new
          min or max of L).
       b. L is full   -> create a new left or right child of L (whichever
          side the search fell off toward) holding just the new value.
  4. Rebalance bottom-up (AVL rotations) from the node that changed, up to
     the root. If a rotation leaves an internal node with fewer than
     MIN_KEYS, fix it immediately via the same GLB-borrow procedure used
     in delete (the paper notes rotations can cause this).

  ===========================================================================
  DELETE
  ===========================================================================
  1. Find the bounding node B of the value; if none, or B doesn't actually
     contain it, no-op.
  2. Erase the value from B's array.
  3. Fix up by B's kind:
       - LEAF: if now empty, detach and delete the node. Otherwise leave
         it (any size 1..MAX_KEYS is valid for a leaf).
       - HALF-LEAF: let C be its one (leaf) child. If
         |B.keys| + |C.keys| <= MAX_KEYS, merge C's keys into B and delete
         C (B becomes a leaf). Otherwise leave both as-is.
       - INTERNAL: if |B.keys| < MIN_KEYS, pull the GLB node's MAXIMUM key
         up into B (filling the gap), then recursively apply the
         leaf/half-leaf fixup above to the GLB node (it just lost its
         max). This borrow-from-predecessor repair -- not a B-tree-style
         subtree merge -- is the defining T-tree delete behavior.

         SUBTLETY: if the borrow empties and deletes the GLB leaf, that
         leaf's PARENT loses a child. This is not merely a node-kind
         change (internal -> half-leaf, or half-leaf -> leaf) -- it can
         also be a genuine AVL imbalance, e.g. an internal node whose
         remaining child is itself a half-leaf-with-a-child now has
         subtree heights differing by 2. A node-kind/merge fixup alone
         cannot repair that; an actual rotation can. So the fixup walks
         from the GLB leaf's parent back up to the borrowing node,
         calling the SAME rebalancing routine used everywhere else
         (rebalanceAt), not just patching node kind or height in place.
  4. Rebalance bottom-up from B (or wherever the structural change
     happened) to the root, re-running the internal-underflow fix after
     any rotation, exactly as in insert.

  ===========================================================================
  INVARIANTS THIS IMPLEMENTATION ENFORCES *AND* VERIFIES
  ===========================================================================
    - MAX_KEYS bound on every node.
    - MIN_KEYS bound on every INTERNAL node (explicitly NOT leaves/half-
      leaves, per the paper).
    - BST-of-ranges invariant across the whole tree.
    - Half-leaf's single child is itself a leaf.
    - GLB/GUB node of any internal node is a leaf or half-leaf (never
      internal) -- this is an emergent property the checker confirms
      holds after every single operation, not just assumed.
    - AVL balance factor in [-1, 1] at every node.
    - Correct height bookkeeping.
    - Correct parent pointers throughout.
*/

const int MAX_KEYS = 4;
const int MIN_KEYS = (MAX_KEYS + 1) / 2;  // internal nodes only

struct TNode {
    vector<int> keys;
    TNode* parent = nullptr;
    TNode* left = nullptr;
    TNode* right = nullptr;
    int height = 1;

    explicit TNode(int val) { keys.push_back(val); }
};

// ===========================================================================
// small helpers
// ===========================================================================

int nodeHeight(TNode* n) { return n ? n->height : 0; }

void updateHeight(TNode* n) {
    if (!n) return;
    n->height = 1 + max(nodeHeight(n->left), nodeHeight(n->right));
}

int balanceFactor(TNode* n) {
    if (!n) return 0;
    return nodeHeight(n->left) - nodeHeight(n->right);
}

bool isLeaf(TNode* n) { return n && !n->left && !n->right; }

bool isHalfLeaf(TNode* n) {
    if (!n) return false;
    int c = (n->left ? 1 : 0) + (n->right ? 1 : 0);
    return c == 1;
}

bool isInternal(TNode* n) { return n && n->left && n->right; }

// Replace `oldChild` with `newChild` in oldChild's parent's child slot.
void replaceChildInParent(TNode* parent, TNode* oldChild, TNode* newChild) {
    if (!parent) return;
    if (parent->left == oldChild) parent->left = newChild;
    else if (parent->right == oldChild) parent->right = newChild;
    if (newChild) newChild->parent = parent;
}

void setLeft(TNode* parent, TNode* child) {
    parent->left = child;
    if (child) child->parent = parent;
}
void setRight(TNode* parent, TNode* child) {
    parent->right = child;
    if (child) child->parent = parent;
}

// ===========================================================================
// GLB / GUB node lookup
// ===========================================================================

TNode* glbNode(TNode* n) {
    if (!n || !n->left) return nullptr;
    TNode* cur = n->left;
    while (cur->right) cur = cur->right;
    return cur;
}

TNode* gubNode(TNode* n) {
    if (!n || !n->right) return nullptr;
    TNode* cur = n->right;
    while (cur->left) cur = cur->left;
    return cur;
}

// ===========================================================================
// internal-node underflow repair (shared by delete and post-rotation fixup)
// ===========================================================================

void fixLeafOrHalfLeafAfterShrink(TNode* node); // fwd decl
bool tryMergeHalfLeaf(TNode* node); // fwd decl

// If `node` is internal and has fewer than MIN_KEYS, pull the GLB node's
// max key up into node, then fix up the GLB node itself (it just lost its
// max -- apply the leaf/half-leaf-merge rule to it).
//
// IMPORTANT subtlety: deleting g (when borrowing empties it) shrinks the
// height of g's side of the tree by one level relative to its sibling,
// which can introduce a genuine AVL imbalance at g's parent (and
// possibly further up) -- not just a node-kind change. For example: an
// internal node with children [half-leaf-with-its-own-child] and [leaf]
// can, after the leaf is deleted, end up with only the half-leaf child
// remaining -- and that half-leaf's own child makes the parent's two
// subtree heights differ by 2. A node-kind fixup (merge) cannot repair
// this; only a rotation can. So this function must call the SAME
// rebalancing machinery used elsewhere (rebalanceAt), not just patch
// heights, along the path from where the structural change happened
// back up to `node`.
TNode* rebalanceAt(TNode* node); // fwd decl (defined in the rotations section below)

void fixInternalUnderflow(TNode* node) {
    if (!isInternal(node)) return;
    if ((int)node->keys.size() >= MIN_KEYS) return;

    TNode* g = glbNode(node);
    if (!g || g->keys.empty()) return; // safety; shouldn't happen structurally

    int borrowed = g->keys.back();
    g->keys.pop_back();
    node->keys.insert(lower_bound(node->keys.begin(), node->keys.end(), borrowed), borrowed);

    TNode* gParentBeforeFix = g->parent; // capture before g potentially gets deleted
    fixLeafOrHalfLeafAfterShrink(g);

    // Rebalance (not just re-height) the side branch from gParentBeforeFix
    // up to `node`, since the structural change on this branch is NOT
    // visited by the caller's main rebalance walk (which starts from a
    // different node entirely). Each level here may need an actual
    // rotation; rebalanceAt() always relinks whatever node ends up at a
    // given position back into that position's ORIGINAL parent slot (see
    // rotateLeft/rotateRight), so walking via ->parent after each call is
    // safe and always converges toward `node`.
    if (gParentBeforeFix && gParentBeforeFix != node) {
        TNode* walk = gParentBeforeFix;
        int guard = 0;
        while (walk && walk != node) {
            TNode* parentBefore = walk->parent;
            rebalanceAt(walk);
            walk = parentBefore;
            if (++guard > 10000) break; // pathological-case safety net; should never trigger
        }
    }
    updateHeight(node);
}

// If `n` is a half-leaf whose array, combined with its single (leaf)
// child's array, fits within MAX_KEYS, merge them (n absorbs the leaf's
// keys and becomes a leaf itself; the child node is deleted). This check
// must be applied EVERYWHERE a half-leaf can arise or be left in a
// mergeable state -- not just after delete-driven shrinkage. That
// includes: right after insert creates a half-leaf, after the
// GLB-borrow in fixInternalUnderflow shrinks one, and after rotations
// reshape the tree. Returns true if a merge happened.
bool tryMergeHalfLeaf(TNode* n) {
    if (!isHalfLeaf(n)) return false;
    TNode* child = n->left ? n->left : n->right;
    if (!isLeaf(child)) return false; // structurally shouldn't happen, but be safe
    if ((int)(n->keys.size() + child->keys.size()) > MAX_KEYS) return false;

    for (int k : child->keys) {
        n->keys.insert(lower_bound(n->keys.begin(), n->keys.end(), k), k);
    }
    if (n->left == child) n->left = nullptr;
    else n->right = nullptr;
    delete child;
    updateHeight(n);
    return true;
}

// After removing a key from a leaf or half-leaf node `n` (shrinking it),
// apply the paper's cleanup rule:
//   - leaf, now empty                 -> detach and delete the node.
//   - half-leaf whose array + child's array fits in MAX_KEYS -> merge.
// Leaves/half-leaves that are simply smaller (but non-empty / non-
// mergeable) are left as-is, since MIN_KEYS does not apply to them.
void fixLeafOrHalfLeafAfterShrink(TNode* n) {
    if (!n) return;

    if (isLeaf(n)) {
        if (n->keys.empty()) {
            TNode* p = n->parent;
            replaceChildInParent(p, n, nullptr);
            delete n;
            if (p) updateHeight(p);
        }
        return;
    }

    if (isHalfLeaf(n)) {
        tryMergeHalfLeaf(n);
        return;
    }
    // n internal: nothing to do here; handled by fixInternalUnderflow.
}

// ===========================================================================
// rotations
// ===========================================================================
//
// Each rotation takes the old subtree root, performs the rotation, and
// fully relinks parent pointers -- including reattaching the new subtree
// root into the ORIGINAL grandparent's child slot. Callers can then walk
// upward via `newSubtreeRoot->parent` without tracking which side of the
// grandparent they came from.

TNode* rotateRight(TNode* y) {
    TNode* gp = y->parent;
    TNode* x = y->left;
    TNode* T2 = x->right;

    setRight(x, y);
    setLeft(y, T2);

    updateHeight(y);
    updateHeight(x);

    replaceChildInParent(gp, y, x);
    if (!gp) x->parent = nullptr;
    return x;
}

TNode* rotateLeft(TNode* x) {
    TNode* gp = x->parent;
    TNode* y = x->right;
    TNode* T2 = y->left;

    setLeft(y, x);
    setRight(x, T2);

    updateHeight(x);
    updateHeight(y);

    replaceChildInParent(gp, x, y);
    if (!gp) y->parent = nullptr;
    return y;
}

// Rebalance exactly at `node` (children assumed already balanced/updated
// by earlier calls further down the path). Returns the node that now
// occupies this tree position (itself, or a new one after rotation).
// Also repairs internal-node underflow a rotation may have introduced,
// per the paper's explicit note about this case.
TNode* rebalanceAt(TNode* node) {
    if (!node) return node;
    updateHeight(node);
    int bf = balanceFactor(node);

    TNode* result = node;
    if (bf > 1) {
        if (balanceFactor(node->left) >= 0) {
            result = rotateRight(node);                 // LL
        } else {
            TNode* newLeft = rotateLeft(node->left);     // LR
            setLeft(node, newLeft);
            updateHeight(node);
            result = rotateRight(node);
        }
    } else if (bf < -1) {
        if (balanceFactor(node->right) <= 0) {
            result = rotateLeft(node);                   // RR
        } else {
            TNode* newRight = rotateRight(node->right);  // RL
            setRight(node, newRight);
            updateHeight(node);
            result = rotateLeft(node);
        }
    }

    if (isInternal(result)) fixInternalUnderflow(result);
    if (isInternal(result->left)) fixInternalUnderflow(result->left);
    if (isInternal(result->right)) fixInternalUnderflow(result->right);

    // A rotation can also leave `result` or its children as a mergeable
    // half-leaf (e.g. a node that picks up a single leaf child post-
    // rotation where it previously had none, or already had one it could
    // now absorb). Check all three positions explicitly rather than
    // assuming only the delete/underflow path can produce this shape.
    if (tryMergeHalfLeaf(result)) updateHeight(result);
    if (result->left && tryMergeHalfLeaf(result->left)) updateHeight(result->left);
    if (result->right && tryMergeHalfLeaf(result->right)) updateHeight(result->right);
    updateHeight(result);

    return result;
}

// Walk from `start` up to the root, rebalancing at every level. Returns
// the new overall root (nullptr if the tree became empty and start was
// itself removed -- callers pass a non-null surviving ancestor in that
// case, see ttree_delete).
TNode* rebalancePathToRoot(TNode* start) {
    if (!start) return nullptr;
    TNode* cur = start;
    TNode* lastSeen = start;
    while (cur) {
        lastSeen = rebalanceAt(cur);
        cur = lastSeen->parent;
    }
    return lastSeen;
}

// ===========================================================================
// search
// ===========================================================================

bool ttree_search(TNode* root, int key) {
    TNode* cur = root;
    while (cur) {
        if (key < cur->keys.front()) {
            cur = cur->left;
        } else if (key > cur->keys.back()) {
            cur = cur->right;
        } else {
            return binary_search(cur->keys.begin(), cur->keys.end(), key);
        }
    }
    return false;
}

// Returns the bounding node for `key`, or nullptr if none exists. Also
// reports the last node visited (used for the no-bounding-node insert
// case) via `outLast`.
TNode* findBoundingNode(TNode* root, int key, TNode** outLast) {
    TNode* cur = root;
    TNode* last = root;
    while (cur) {
        last = cur;
        if (key < cur->keys.front()) {
            cur = cur->left;
        } else if (key > cur->keys.back()) {
            cur = cur->right;
        } else {
            if (outLast) *outLast = cur;
            return cur;
        }
    }
    if (outLast) *outLast = last;
    return nullptr;
}

// ===========================================================================
// insert
// ===========================================================================

TNode* ttree_insert(TNode* root, int key) {
    if (!root) return new TNode(key);
    if (ttree_search(root, key)) return root; // duplicates rejected

    TNode* last = nullptr;
    TNode* bounding = findBoundingNode(root, key, &last);
    TNode* changed = nullptr;

    if (bounding) {
        TNode* B = bounding;
        if ((int)B->keys.size() < MAX_KEYS) {
            B->keys.insert(lower_bound(B->keys.begin(), B->keys.end(), key), key);
            updateHeight(B);
            changed = B;
        } else {
            // Full bounding node: evict current min, insert new key,
            // then try to push the evicted value into the GLB node
            // before resorting to creating a brand new node.
            int evicted = B->keys.front();
            B->keys.erase(B->keys.begin());
            B->keys.insert(lower_bound(B->keys.begin(), B->keys.end(), key), key);
            updateHeight(B);

            TNode* g = glbNode(B);
            if (g) {
                if ((int)g->keys.size() < MAX_KEYS) {
                    g->keys.push_back(evicted);
                    updateHeight(g);
                    changed = g;
                } else {
                    TNode* newNode = new TNode(evicted);
                    setRight(g, newNode);
                    updateHeight(g);
                    changed = newNode;
                }
            } else {
                // No left subtree at all under B -> nothing can hold a
                // value below B's range except a new left child of B.
                TNode* newNode = new TNode(evicted);
                setLeft(B, newNode);
                updateHeight(B);
                changed = newNode;
            }
        }
    } else {
        TNode* L = last;
        if (key < L->keys.front()) {
            if ((int)L->keys.size() < MAX_KEYS) {
                L->keys.insert(L->keys.begin(), key);
                updateHeight(L);
                changed = L;
            } else {
                TNode* newNode = new TNode(key);
                setLeft(L, newNode);
                updateHeight(L);
                changed = newNode;
            }
        } else { // key > L->keys.back()
            if ((int)L->keys.size() < MAX_KEYS) {
                L->keys.push_back(key);
                updateHeight(L);
                changed = L;
            } else {
                TNode* newNode = new TNode(key);
                setRight(L, newNode);
                updateHeight(L);
                changed = newNode;
            }
        }
    }

    return rebalancePathToRoot(changed);
}

// ===========================================================================
// delete
// ===========================================================================

TNode* ttree_delete(TNode* root, int key) {
    if (!root) return root;

    TNode* last = nullptr;
    TNode* B = findBoundingNode(root, key, &last);
    if (!B) return root;
    auto it = lower_bound(B->keys.begin(), B->keys.end(), key);
    if (it == B->keys.end() || *it != key) return root; // not actually present

    B->keys.erase(it);
    TNode* changed = B;     // node from which rebalancing should start
    bool treeNowEmpty = false;

    if (isLeaf(B)) {
        if (B->keys.empty()) {
            TNode* p = B->parent;
            if (!p) {
                // B was the root and is now empty with no children: tree
                // becomes empty.
                delete B;
                treeNowEmpty = true;
                changed = nullptr;
            } else {
                replaceChildInParent(p, B, nullptr);
                delete B;
                changed = p;
            }
        } else {
            updateHeight(B);
        }
    } else if (isHalfLeaf(B)) {
        updateHeight(B);
        tryMergeHalfLeaf(B);
    } else {
        // internal
        updateHeight(B);
        fixInternalUnderflow(B);
    }

    if (treeNowEmpty) return nullptr;
    return rebalancePathToRoot(changed);
}

// ===========================================================================
// printing / traversal
// ===========================================================================

string kindOf(TNode* n) {
    if (isLeaf(n)) return "leaf";
    if (isHalfLeaf(n)) return "half-leaf";
    if (isInternal(n)) return "internal";
    return "?";
}

void printTTree(TNode* root, const string& prefix = "") {
    if (!root) return;
    cout << prefix << "[";
    for (size_t i = 0; i < root->keys.size(); ++i) {
        cout << root->keys[i];
        if (i + 1 < root->keys.size()) cout << ",";
    }
    cout << "] (h=" << root->height << ", " << kindOf(root) << ")\n";
    if (root->left)  printTTree(root->left,  prefix + "  L-");
    if (root->right) printTTree(root->right, prefix + "  R-");
}

void inorderCollect(TNode* root, vector<int>& out) {
    if (!root) return;
    inorderCollect(root->left, out);
    for (int k : root->keys) out.push_back(k);
    inorderCollect(root->right, out);
}

void freeTree(TNode* root) {
    if (!root) return;
    freeTree(root->left);
    freeTree(root->right);
    delete root;
}

// ===========================================================================
// invariant checker
// ===========================================================================
//
// Verifies, at minimum, everything flagged as missing in the prior review:
//   - MAX_KEYS bound on every node.
//   - MIN_KEYS bound specifically on INTERNAL nodes (not leaves/half-leaves
//     -- the checker treats that exemption as correct per the paper, and
//     instead checks that leaves/half-leaves are NEVER required to meet
//     MIN_KEYS, while asserting internal nodes ALWAYS are).
//   - half-leaf's single child is a leaf, AND (per the merge rule) that a
//     half-leaf + its child could NOT be merged without exceeding MAX_KEYS
//     (if they could be merged, that's itself an invariant violation,
//     since fixLeafOrHalfLeafAfterShrink should have merged them already).
//   - BST-of-ranges, AVL balance, height bookkeeping (as before).
//   - parent pointers consistent with child pointers everywhere.
//   - GLB/GUB node of every internal node is itself a leaf or half-leaf
//     (never internal) -- an emergent structural property of the paper's
//     algorithm, checked rather than assumed.

struct CheckResult {
    bool ok = true;
    vector<string> errors;
};

void checkInvariants(TNode* node, TNode* expectedParent,
                      const optional<int>& lowBound, const optional<int>& highBound,
                      CheckResult& res) {
    if (!node) return;

    if (node->keys.empty()) {
        res.ok = false;
        res.errors.push_back("Node with empty keys array found");
        return;
    }
    if ((int)node->keys.size() > MAX_KEYS) {
        res.ok = false;
        res.errors.push_back("Node exceeds MAX_KEYS: size=" + to_string(node->keys.size()) +
                              " min=" + to_string(node->keys.front()));
    }
    for (size_t i = 1; i < node->keys.size(); ++i) {
        if (node->keys[i] <= node->keys[i - 1]) {
            res.ok = false;
            res.errors.push_back("Node keys not strictly sorted/unique at min=" +
                                  to_string(node->keys.front()));
        }
    }
    if (lowBound && node->keys.front() <= *lowBound) {
        res.ok = false;
        res.errors.push_back("BST-range violation: node min " + to_string(node->keys.front()) +
                              " <= ancestor bound " + to_string(*lowBound));
    }
    if (highBound && node->keys.back() >= *highBound) {
        res.ok = false;
        res.errors.push_back("BST-range violation: node max " + to_string(node->keys.back()) +
                              " >= ancestor bound " + to_string(*highBound));
    }

    if (node->parent != expectedParent) {
        res.ok = false;
        res.errors.push_back("Parent pointer mismatch at node with min=" +
                              to_string(node->keys.front()));
    }

    // ---- node-kind specific checks ----
    if (isHalfLeaf(node)) {
        TNode* child = node->left ? node->left : node->right;
        if (!isLeaf(child)) {
            res.ok = false;
            res.errors.push_back("Half-leaf's single child is not itself a leaf "
                                  "(node min=" + to_string(node->keys.front()) + ")");
        } else {
            // Per the merge rule, a half-leaf that COULD merge with its
            // child without exceeding MAX_KEYS should already have been
            // merged. If we find one that could still merge, that's a
            // bug, not an acceptable state.
            if ((int)(node->keys.size() + child->keys.size()) <= MAX_KEYS) {
                res.ok = false;
                res.errors.push_back("Half-leaf at min=" + to_string(node->keys.front()) +
                                      " could merge with its child (sizes " +
                                      to_string(node->keys.size()) + "+" +
                                      to_string(child->keys.size()) + " <= MAX_KEYS=" +
                                      to_string(MAX_KEYS) + ") but was left unmerged");
            }
        }
    }

    if (isInternal(node)) {
        if ((int)node->keys.size() < MIN_KEYS) {
            res.ok = false;
            res.errors.push_back("Internal node below MIN_KEYS: size=" +
                                  to_string(node->keys.size()) + " < MIN_KEYS=" +
                                  to_string(MIN_KEYS) + " (min key=" +
                                  to_string(node->keys.front()) + ")");
        }
        // GLB/GUB node must be a leaf or half-leaf, never internal.
        TNode* g = glbNode(node);
        if (g && isInternal(g)) {
            res.ok = false;
            res.errors.push_back("GLB node of internal node (min=" +
                                  to_string(node->keys.front()) + ") is itself internal "
                                  "-- violates T-tree structural guarantee");
        }
        TNode* u = gubNode(node);
        if (u && isInternal(u)) {
            res.ok = false;
            res.errors.push_back("GUB node of internal node (min=" +
                                  to_string(node->keys.front()) + ") is itself internal "
                                  "-- violates T-tree structural guarantee");
        }
    }
    // NOTE: leaves and half-leaves are intentionally NOT checked against
    // MIN_KEYS -- the paper explicitly exempts them. A leaf or half-leaf
    // with just 1 key is valid and expected.

    checkInvariants(node->left, node, lowBound, optional<int>(node->keys.front()), res);
    checkInvariants(node->right, node, optional<int>(node->keys.back()), highBound, res);

    int expectedHeight = 1 + max(nodeHeight(node->left), nodeHeight(node->right));
    if (node->height != expectedHeight) {
        res.ok = false;
        res.errors.push_back("Height mismatch at node min=" + to_string(node->keys.front()) +
                              ": stored=" + to_string(node->height) +
                              " expected=" + to_string(expectedHeight));
    }

    int bf = balanceFactor(node);
    if (bf < -1 || bf > 1) {
        res.ok = false;
        res.errors.push_back("AVL balance violated at node min=" +
                              to_string(node->keys.front()) + ": bf=" + to_string(bf));
    }
}

CheckResult verifyTree(TNode* root) {
    CheckResult res;
    if (root && root->parent != nullptr) {
        res.ok = false;
        res.errors.push_back("Root's parent pointer is not null");
    }
    checkInvariants(root, nullptr, nullopt, nullopt, res);
    return res;
}

// ===========================================================================
// demo
// ===========================================================================

void runDemo() {
    TNode* root = nullptr;
    vector<int> vals = {10, 5, 15, 20, 8, 12, 18, 25, 3, 6, 30, 1, 22, 17, 4, 9, 11, 13, 19, 21};

    cout << "MAX_KEYS=" << MAX_KEYS << "  MIN_KEYS(internal only)=" << MIN_KEYS << "\n";
    cout << "Inserting:";
    for (int v : vals) cout << " " << v;
    cout << "\n\n";

    for (int v : vals) root = ttree_insert(root, v);

    cout << "Tree after inserts:\n";
    printTTree(root);

    vector<int> sorted = vals;
    sort(sorted.begin(), sorted.end());
    sorted.erase(unique(sorted.begin(), sorted.end()), sorted.end());
    vector<int> got;
    inorderCollect(root, got);
    cout << "\nInorder matches expected: " << (got == sorted ? "YES" : "NO") << "\n";

    CheckResult res = verifyTree(root);
    cout << "Invariants after insert: " << (res.ok ? "ALL HOLD" : "VIOLATED") << "\n";
    for (auto& e : res.errors) cout << "  - " << e << "\n";

    cout << "\nNow deleting: 8, 17, 30, 1, 15 (root key), 10\n";
    for (int v : {8, 17, 30, 1, 15, 10}) {
        root = ttree_delete(root, v);
        CheckResult r2 = verifyTree(root);
        cout << "  after delete(" << v << "): invariants " << (r2.ok ? "OK" : "VIOLATED");
        if (!r2.ok) for (auto& e : r2.errors) cout << "\n      - " << e;
        cout << "\n";
    }

    cout << "\nTree after deletes:\n";
    printTTree(root);

    vector<int> got2;
    inorderCollect(root, got2);
    cout << "\nRemaining (inorder): ";
    for (int x : got2) cout << x << " ";
    cout << "\n";

    freeTree(root);
}

// Fuzz test: random mix of inserts and deletes, checking ALL invariants
// after every single operation.
bool fuzzTest(int numTrees, int opsPerTree, int keyRange, double deleteProb, unsigned seed,
              bool verboseLog = false) {
    mt19937 rng(seed);
    uniform_real_distribution<double> coin(0.0, 1.0);

    for (int t = 0; t < numTrees; ++t) {
        TNode* root = nullptr;
        set<int> reference;
        uniform_int_distribution<int> dist(0, keyRange - 1);
        vector<pair<char,int>> log; // for replay on failure

        for (int i = 0; i < opsPerTree; ++i) {
            int key = dist(rng);
            bool doDelete = !reference.empty() && coin(rng) < deleteProb;

            if (doDelete) {
                // bias toward deleting a key that actually exists, half the time
                if (coin(rng) < 0.5) {
                    auto it = reference.begin();
                    advance(it, uniform_int_distribution<int>(0, (int)reference.size() - 1)(rng));
                    key = *it;
                }
                root = ttree_delete(root, key);
                reference.erase(key);
                log.push_back({'D', key});
            } else {
                root = ttree_insert(root, key);
                reference.insert(key);
                log.push_back({'I', key});
            }

            CheckResult res = verifyTree(root);
            if (!res.ok) {
                cout << "FUZZ FAILURE: tree #" << t << " op#" << i
                     << " (" << (doDelete ? "delete" : "insert") << " " << key << ")\n";
                for (auto& e : res.errors) cout << "    - " << e << "\n";
                cout << "  Tree:\n";
                printTTree(root, "    ");
                if (verboseLog) {
                    cout << "  Replay log (" << log.size() << " ops):\n    ";
                    for (auto& [op, k] : log) cout << op << k << " ";
                    cout << "\n";
                }
                freeTree(root);
                return false;
            }

            vector<int> got;
            inorderCollect(root, got);
            vector<int> expected(reference.begin(), reference.end());
            if (got != expected) {
                cout << "FUZZ FAILURE: tree #" << t << " op#" << i << " inorder mismatch\n";
                cout << "  expected:"; for (int x : expected) cout << " " << x; cout << "\n";
                cout << "  got:     "; for (int x : got) cout << " " << x; cout << "\n";
                freeTree(root);
                return false;
            }

            for (int q : expected) {
                if (!ttree_search(root, q)) {
                    cout << "FUZZ FAILURE: tree #" << t << " key " << q << " missing from search\n";
                    freeTree(root);
                    return false;
                }
            }
            // also confirm deleted/never-inserted keys are NOT found
            // (sample a few per iteration to keep cost down)
            for (int s = 0; s < 3; ++s) {
                int q = dist(rng);
                bool shouldFind = reference.count(q) > 0;
                if (ttree_search(root, q) != shouldFind) {
                    cout << "FUZZ FAILURE: tree #" << t << " search(" << q << ") wrong: "
                         << "got " << ttree_search(root, q) << " expected " << shouldFind << "\n";
                    freeTree(root);
                    return false;
                }
            }
        }
        freeTree(root);
    }
    return true;
}

// ===========================================================================
// regression tests
// ===========================================================================
//
// Specific scenarios that were found, by fuzzing, to break earlier
// versions of this implementation. Kept as permanent, fast, targeted
// checks so a future refactor can't silently reintroduce them.

bool regressionTests() {
    bool allOk = true;

    // Regression #1: deleting a key whose bounding node is the root can
    // trigger an internal-underflow GLB-borrow that empties and deletes
    // the GLB leaf. That leaf's parent then loses a child and can be left
    // with its OTHER child being a half-leaf (not a leaf) -- which is an
    // illegal half-leaf shape AND a genuine AVL imbalance (bf=2) that only
    // a rotation can fix, not a merge. An earlier version of this code
    // only re-checked for a possible merge after such a deletion, which
    // can't repair this case, leaving an invalid tree.
    //
    // Sequence reconstructed from a fuzz failure (seed=6 config, op#361):
    // build up a tree, then delete the root's key 33, where the GLB chain
    // walks through a half-leaf-with-child before reaching its leaf.
    {
        TNode* root = nullptr;
        struct Op { char kind; int key; };
        vector<Op> ops = {
            {'I',44},{'D',44},{'I',30},{'I',24},{'D',30},{'D',40},{'I',2},{'I',36},
            {'I',6},{'I',10},{'I',12},{'I',35},{'D',12},{'I',20},{'I',18},{'I',19},
            {'D',35},{'D',12},{'D',27},{'D',18},{'I',41},{'D',10},{'I',21},{'D',34},
            {'D',19},{'I',42},{'I',5},{'D',6},{'D',41},{'I',6},{'D',38},{'I',2},
            {'I',46},{'D',24},{'I',27},{'I',3},{'D',15},{'D',5},{'I',1},{'D',42},
            {'I',36},{'I',21},{'I',47},{'D',12},{'D',27},{'I',25},{'D',41},{'D',39},
            {'D',1},{'D',7},{'I',42},{'I',45},{'I',0},{'D',3},{'I',37},{'D',0},
            {'I',32},{'I',39},{'I',8},{'I',42},{'D',45},{'I',5},{'I',22},{'I',9},
            {'D',46},{'I',39},{'I',12},{'D',29},{'D',13},{'D',42},{'I',41},{'D',9},
            {'I',32},{'I',12},{'I',31},{'I',36},{'I',28},{'D',13},{'D',21},{'D',29},
            {'D',39},{'D',37},{'I',13},{'I',7},{'I',30},{'D',5},{'I',9},{'D',38},
            {'D',30},{'D',12},{'D',19},{'I',37},{'I',31},{'D',2},{'I',15},{'I',38},
            {'D',36},{'D',31},{'D',34},{'D',38},{'D',44},{'I',21},{'I',10},{'D',5},
            {'I',16},{'D',4},{'I',11},{'D',15},{'I',29},{'D',32},{'I',38},{'D',14},
            {'D',36},{'D',41},{'D',44},{'D',16},{'I',4},{'I',44},{'D',16},{'D',7},
            {'I',40},{'I',37},{'I',32},{'D',4},{'D',8},{'I',49},{'I',32},{'I',16},
            {'D',36},{'D',42},{'I',21},{'I',27},{'I',17},{'I',13},{'I',22},{'D',47},
            {'I',15},{'I',46},{'D',28},{'I',41},{'D',44},{'D',20},{'I',12},{'I',5},
            {'I',0},{'I',34},{'I',15},{'D',6},{'D',10},{'D',29},{'I',20},{'I',20},
            {'I',21},{'D',7},{'I',14},{'D',5},{'I',18},{'D',24},{'I',2},{'I',14},
            {'D',4},{'I',4},{'D',46},{'D',34},{'I',38},{'I',45},{'D',32},{'D',16},
            {'D',10},{'D',26},{'D',27},{'D',0},{'I',8},{'I',28},{'D',21},{'D',45},
            {'I',8},{'I',27},{'I',12},{'I',4},{'I',9},{'I',41},{'D',36},{'D',14},
            {'I',21},{'I',17},{'D',32},{'I',17},{'I',19},{'D',28},{'I',36},{'I',18},
            {'I',9},{'I',40},{'D',9},{'I',30},{'D',8},{'I',35},{'I',44},{'I',13},
            {'D',13},{'D',42},{'D',18},{'D',41},{'D',41},{'D',49},{'I',13},{'I',19},
            {'I',44},{'I',35},{'I',5},{'D',40},{'I',21},{'D',25},{'D',11},{'I',39},
            {'D',39},{'I',26},{'D',19},{'I',46},{'D',34},{'I',6},{'D',26},{'I',15},
            {'I',44},{'D',12},{'I',46},{'D',48},{'D',4},{'D',35},{'I',20},{'D',44},
            {'D',46},{'I',13},{'I',16},{'D',21},{'D',44},{'D',49},{'I',24},{'I',37},
            {'I',30},{'D',6},{'D',4},{'I',10},{'I',39},{'D',10},{'I',46},{'D',3},
            {'I',13},{'D',27},{'I',20},{'I',11},{'D',6},{'D',4},{'D',37},{'D',15},
            {'D',5},{'D',49},{'D',17},{'D',12},{'D',39},{'D',24},{'D',20},{'D',40},
            {'I',32},{'I',23},{'D',43},{'I',15},{'D',14},{'D',23},{'D',46},{'I',1},
            {'I',7},{'I',31},{'D',42},{'I',15},{'I',12},{'D',12},{'D',13},{'D',7},
            {'D',43},{'I',20},{'D',22},{'I',27},{'I',43},{'I',10},{'D',2},{'D',45},
            {'D',15},{'D',35},{'D',29},{'D',11},{'D',44},{'I',16},{'I',45},{'D',17},
            {'D',25},{'D',31},{'D',9},{'I',16},{'I',34},{'D',36},{'D',38},{'I',40},
            {'D',20},{'I',41},{'D',0},{'D',10},{'I',33},{'D',40},{'D',33},{'D',43},
            {'I',27},{'I',45},{'I',39},{'D',30},{'D',32},{'I',49},{'I',32},{'D',27},
            {'D',23},{'I',9},{'I',20},{'I',18},{'I',33},{'D',0},{'D',30},{'I',13},
            {'D',45},{'I',42},{'D',34},{'I',45},{'I',25},{'I',33},{'I',11},{'D',16},
            {'I',27},{'D',18},{'I',20},{'I',41},{'D',42},{'I',16},{'I',47},{'D',25},
            {'I',36},{'I',22},{'D',13},{'I',10},{'I',44},{'I',27},{'I',18},{'D',16},
            {'D',8},{'I',18},{'D',44},{'D',35},{'I',19},{'I',6},{'I',40},{'D',27},
            {'I',2},{'D',33}
        };
        for (auto& op : ops) {
            root = (op.kind == 'I') ? ttree_insert(root, op.key) : ttree_delete(root, op.key);
        }
        CheckResult res = verifyTree(root);
        if (!res.ok) {
            cout << "REGRESSION #1 FAILED (half-leaf-chain / AVL imbalance after "
                    "GLB-borrow deletion):\n";
            for (auto& e : res.errors) cout << "    - " << e << "\n";
            allOk = false;
        } else {
            cout << "Regression #1 (GLB-borrow cascading imbalance): PASS\n";
        }
        freeTree(root);
    }

    return allOk;
}

int main(int argc, char** argv) {
    if (argc > 1 && string(argv[1]) == "replay") {
        // Usage: ./ttree replay I5 I10 D5 I3 ...
        TNode* root = nullptr;
        for (int i = 2; i < argc; ++i) {
            string tok = argv[i];
            char op = tok[0];
            int key = stoi(tok.substr(1));
            if (op == 'I') root = ttree_insert(root, key);
            else root = ttree_delete(root, key);

            CheckResult res = verifyTree(root);
            cout << "after " << op << key << ": " << (res.ok ? "OK" : "VIOLATION");
            if (!res.ok) { cout << "\n"; for (auto& e : res.errors) cout << "  - " << e << "\n"; }
            else cout << "\n";
        }
        cout << "\nFinal tree:\n";
        printTTree(root);
        freeTree(root);
        return 0;
    }

    if (argc > 1 && string(argv[1]) == "fuzz") {
        cout << "Running regression tests...\n";
        bool regressionOk = regressionTests();
        cout << (regressionOk ? "All regression tests passed.\n\n" : "REGRESSION TESTS FAILED.\n\n");

        cout << "Running fuzz tests (insert + delete mixed)...\n";
        struct Cfg { int trees, ops, range; double delProb; unsigned seed; bool verbose = false; };
        vector<Cfg> configs = {
            {20, 80,   30,    0.3, 1},
            {20, 300,  1000,  0.3, 2},
            {5,  3000, 5000,  0.4, 3},
            {10, 150,  5,     0.5, 4},   // tiny range, heavy collision + churn
            {10, 600,  10000, 0.3, 5},
            {10, 500,  50,    0.5, 6},   // small range, lots of delete/reinsert churn
            {3,  5000, 200,   0.5, 7},   // long-running churn on a small key space
            {15, 1000, 80,    0.6, 8},   // higher delete bias
            {15, 1000, 80,    0.5, 9},
            {15, 1000, 80,    0.5, 10},
            {5,  8000, 300,   0.5, 11},  // very long churn, small space
            {30, 60,   20,    0.7, 12},  // tiny trees, heavy churn, many trials
            {2,  20000,2000,  0.45,13},  // very long single-tree stress
            {20, 2000, 150,   0.55,101},
            {20, 2000, 150,   0.55,202},
            {20, 2000, 150,   0.55,303},
            {8,  10000,500,   0.5, 404},
            {50, 200,  40,    0.6, 505},
        };
        bool allPass = regressionOk;
        for (auto& c : configs) {
            bool ok = fuzzTest(c.trees, c.ops, c.range, c.delProb, c.seed, c.verbose);
            cout << "  config(trees=" << c.trees << ", ops=" << c.ops << ", range=" << c.range
                 << ", delProb=" << c.delProb << ", seed=" << c.seed << ") -> "
                 << (ok ? "PASS" : "FAIL") << "\n";
            allPass &= ok;
        }
        cout << (allPass ? "\nALL TESTS PASSED\n" : "\nSOME TESTS FAILED\n");
        return allPass ? 0 : 1;
    }

    runDemo();
    return 0;
}