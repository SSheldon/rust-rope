#![feature(collections, core)]

//! A rope for efficiently storing and manipulating large amounts of text.

use std::borrow::Cow;
use std::cmp::{max, Ordering};
use std::default::Default;
use std::fmt;
use std::mem;
use std::string::CowString;

use self::Node::{Nil, Leaf, Branch};

/// A `Rope` is a tree of `String`s that allows more efficient storage and
/// manipulation of large amounts of text than a `String`.
pub struct Rope {
    root: Node,
}

impl Rope {
    /// Creates a new, empty `Rope`.
    #[inline]
    pub fn new() -> Rope {
        Rope { root: Nil }
    }

    /// Creates a new `Rope` from the given `String`.
    #[inline]
    pub fn from_string(string: String) -> Rope {
        Rope { root: if string.len() > 0 { Leaf(string) } else { Nil } }
    }

    /// Take the root of the `Rope`, replacing it with `Nil`.
    #[inline]
    fn take_root(&mut self) -> Node {
        mem::replace(&mut self.root, Nil)
    }

    /// Append `rope` to the end of the `Rope`.
    #[inline]
    pub fn append(&mut self, rope: Rope) {
        if rope.len() > 0 {
            let root = self.take_root();
            self.root = Node::concat(root, rope.root);
        }
    }

    /// Appends `string` to the end of the `Rope`.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let mut rope = Rope::from_string("ab".to_string());
    /// rope.append_string("cd".to_string());
    /// assert!(&rope == "abcd");
    /// ```
    #[inline]
    pub fn append_string(&mut self, string: String) {
        self.append(Rope::from_string(string));
    }

    /// Prepends `rope` to the beginning of the `Rope`.
    #[inline]
    pub fn prepend(&mut self, rope: Rope) {
        if rope.len() > 0 {
            let root = self.take_root();
            self.root = Node::concat(rope.root, root);
        }
    }

    /// Prepends `string` to the beginning of the `Rope`.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let mut rope = Rope::from_string("ab".to_string());
    /// rope.prepend_string("cd".to_string());
    /// assert!(&rope == "cdab");
    /// ```
    #[inline]
    pub fn prepend_string(&mut self, string: String) {
        self.prepend(Rope::from_string(string));
    }

    /// Splits the `Rope` into two `Rope`s at the given `index`.
    /// Returns the pair of `Rope`s to the left and right of the split.
    ///
    /// # Failure
    ///
    /// If `index` is greater than the length of the `Rope`.
    /// If `index` is not a valid character boundary.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let rope = Rope::from_string("abcd".to_string());
    /// let (left, right) = rope.split(2);
    /// assert!(&left == "ab");
    /// assert!(&right == "cd");
    /// ```
    #[inline]
    pub fn split(self, index: usize) -> (Rope, Rope) {
        assert!(index <= self.len());
        let (left, right) = self.root.split(index);
        (Rope { root: left }, Rope { root: right })
    }

    /// Inserts `rope` at `index` into the `Rope`.
    ///
    /// # Failure
    ///
    /// If `index` is greater than the length of the `Rope`.
    /// If `index` is not a valid character boundary.
    pub fn insert(&mut self, index: usize, rope: Rope) {
        let len = self.len();
        if index == 0 {
            self.prepend(rope);
        } else if index == len {
            self.append(rope);
        } else if rope.len() > 0 {
            assert!(index <= len);
            let root = self.take_root();
            let (left, right) = root.split(index);
            // Concat our inserted rope with the left split
            let left = Node::concat(left, rope.root);
            self.root = Node::concat(left, right);
        }
    }

    /// Inserts `string` at `index` into the `Rope`.
    ///
    /// # Failure
    ///
    /// If `index` is greater than the length of the `Rope`.
    /// If `index` is not a valid character boundary.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let mut rope = Rope::from_string("ab".to_string());
    /// rope.insert_string(1, "cd".to_string());
    /// assert!(&rope == "acdb");
    /// ```
    #[inline]
    pub fn insert_string(&mut self, index: usize, string: String) {
        self.insert(index, Rope::from_string(string));
    }

    /// Deletes the substring of the `Rope` from `start` to `end`.
    /// Returns a `Rope` of the deleted substring.
    ///
    /// # Failure
    ///
    /// If `start` > `end`.
    /// If `start` or `end` is greater than the length of the `Rope`.
    /// If `start` or `end` is not a valid character boundary.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let mut rope = Rope::from_string("abcd".to_string());
    /// rope.delete(1, 3);
    /// assert!(&rope == "ad");
    /// ```
    pub fn delete(&mut self, start: usize, end: usize) -> Rope {
        assert!(start <= end && end <= self.len());
        if start == end {
            // Why are you trying to delete nothing? Don't modify the rope
            Rope::new()
        } else {
            let root = self.take_root();
            // Extract ropes left and right of the deletion
            let (left, right) = root.split(end);
            let (left, deleted) = left.split(start);
            self.root = Node::concat(left, right);
            Rope { root: deleted }
        }
    }

    /// Truncates the `Rope` to only the substring from `start` to `end`.
    /// Returns the pair of `Rope`s removed from the beginning and end
    /// of the `Rope`.
    ///
    /// # Failure
    ///
    /// If `start` > `end`.
    /// If `start` or `end` is greater than the length of the `Rope`.
    /// If `start` or `end` is not a valid character boundary.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let mut rope = Rope::from_string("abcd".to_string());
    /// rope.truncate(1, 3);
    /// assert!(&rope == "bc");
    /// ```
    pub fn truncate(&mut self, start: usize, end: usize) -> (Rope, Rope) {
        assert!(start <= end && end <= self.len());
        let root = self.take_root();
        // Extract ropes to the left and right of the truncation
        let (left, right) = root.split(end);
        let (left, middle) = left.split(start);
        self.root = middle;
        (Rope { root: left }, Rope { root: right })
    }

    /// Returns the substring of the `Rope` from `start` to `end`.
    ///
    /// # Failure
    ///
    /// If `start` > `end`.
    /// If `start` or `end` is greater than the length of the `Rope`.
    /// If `start` or `end` is not a valid character boundary.
    ///
    /// # Example
    ///
    /// ``` rust
    /// use rope::Rope;
    /// let rope = Rope::from_string("abcd".to_string());
    /// assert!(rope.substring(0, 2) == "ab");
    /// assert!(rope.substring(2, 4) == "cd");
    /// ```
    #[inline]
    pub fn substring(&self, start: usize, end: usize) -> CowString {
        assert!(start <= end && end <= self.len());
        let mut substrings = RopeSubstrings::new(&self.root, start, end);
        let first = match substrings.next() {
            None => return Cow::Borrowed(""),
            Some(s) => s,
        };
        match substrings.next() {
            None => Cow::Borrowed(first),
            Some(second) => {
                let mut result = String::with_capacity(end - start);
                result.push_str(first);
                result.push_str(second);
                for part in substrings {
                    result.push_str(part);
                }
                Cow::Owned(result)
            }
        }
    }

    /// Returns an iterator over the strings of the `Rope`.
    #[inline]
    pub fn strings(&self) -> RopeStrings {
        RopeStrings { stack: vec!(&self.root) }
    }

    /// Returns a consuming iterator over the strings of the `Rope`.
    #[inline]
    pub fn into_strings(self) -> RopeMoveStrings {
        RopeMoveStrings { stack: vec!(self.root) }
    }

    fn eq_bytes<T: Iterator<Item=u8>>(&self, bytes: T, len: usize) -> bool {
        if self.len() == len {
            let self_bytes = self.strings().flat_map(|s| s.bytes());
            self_bytes.zip(bytes).all(|(a, b)| a == b)
        } else {
            false
        }
    }

    /// Compares the `Rope` against the `bytes` with the given `len`.
    fn cmp_bytes<T: Iterator<Item=u8>>(&self, bytes: T, len: usize) -> Ordering {
        let self_bytes = self.strings().flat_map(|s| s.bytes());
        for (s_b, o_b) in self_bytes.zip(bytes) {
            match s_b.cmp(&o_b) {
                Ordering::Greater => return Ordering::Greater,
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => (),
            }
        }
        self.len().cmp(&len)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.root.len()
    }

    #[inline]
    pub fn clear(&mut self) {
        self.take_root();
    }
}

impl Ord for Rope {
    #[inline]
    fn cmp(&self, other: &Rope) -> Ordering {
        let other_bytes = other.strings().flat_map(|s| s.bytes());
        self.cmp_bytes(other_bytes, other.len())
    }
}

impl PartialOrd for Rope {
    #[inline]
    fn partial_cmp(&self, other: &Rope) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for Rope { }

impl PartialEq for Rope {
    #[inline]
    fn eq(&self, other: &Rope) -> bool {
        let other_bytes = other.strings().flat_map(|s| s.bytes());
        self.eq_bytes(other_bytes, other.len())
    }
}

impl PartialOrd<str> for Rope {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        Some(self.cmp_bytes(other.bytes(), other.len()))
    }
}

impl PartialEq<str> for Rope {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.eq_bytes(other.bytes(), other.len())
    }
}

impl Default for Rope {
    #[inline]
    fn default() -> Rope {
        Rope::new()
    }
}

impl fmt::Display for Rope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.strings()
            .map(|s| fmt::Display::fmt(s, f))
            .take_while(|r| r.is_ok())
            .last()
            .unwrap_or(Ok(()))
    }
}

enum Node {
    Nil,
    Leaf(String),
    Branch(Box<Concat>),
}

impl Node {
    #[inline]
    fn concat(left: Node, right: Node) -> Node {
        match (left, right) {
            (Nil, r) => r,
            (l, Nil) => l,
            (l, r) => Branch(Box::new(Concat::new(l, r))),
        }
    }

    #[inline]
    fn height(&self) -> usize {
        match *self {
            Nil => 0,
            Leaf(_) => 1,
            Branch(ref cat) => cat.height,
        }
    }

    fn split(self, index: usize) -> (Node, Node) {
        if index == 0 {
            return (Nil, self)
        } else if index == self.len() {
            return (self, Nil)
        } else {
            match self {
                Nil => (Nil, Nil),
                Leaf(s) => {
                    let right = s[index..].to_string();
                    let mut left = s;
                    left.truncate(index);
                    (Leaf(left), Leaf(right))
                }
                Branch(mut cat) => {
                    let left_len = cat.left.len();
                    if index < left_len {
                        let left = cat.split_left(index);
                        // Check if cat no longer has a left child
                        let right = if let Nil = cat.left {
                            cat.right
                        } else {
                            Branch(cat)
                        };
                        (left, right)
                    } else {
                        let right = cat.split_right(index - left_len);
                        // Check if cat no longer has a right child
                        let left = if let Nil = cat.right {
                            cat.left
                        } else {
                            Branch(cat)
                        };
                        (left, right)
                    }
                }
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        match *self {
            Nil => 0,
            Leaf(ref s) => s.len(),
            Branch(ref cat) => cat.len,
        }
    }
}

/// A `Concat` is a concatenation of two `Rope`s;
/// `Concat`s are the internal nodes of the `Rope`'s tree.
struct Concat {
    len: usize,
    height: usize,
    left: Node,
    right: Node,
}

impl Concat {
    #[inline]
    fn new(left: Node, right: Node) -> Concat {
        Concat {
            len: left.len() + right.len(),
            height: max(left.height(), right.height()) + 1,
            left: left,
            right: right,
        }
    }

    #[inline]
    fn update(&mut self) {
        self.len = self.left.len() + self.right.len();
        self.height = max(self.left.height(), self.right.height()) + 1;
    }

    #[inline]
    fn split_left(&mut self, index: usize) -> Node {
        let left = mem::replace(&mut self.left, Nil);
        let (ll, lr) = left.split(index);
        self.left = lr;
        self.update();
        ll
    }

    #[inline]
    fn split_right(&mut self, index: usize) -> Node {
        let right = mem::replace(&mut self.right, Nil);
        let (rl, rr) = right.split(index);
        self.right = rl;
        self.update();
        rr
    }
}

/// Iterator over the strings of a `Rope`.
pub struct RopeStrings<'a> {
    stack: Vec<&'a Node>,
}

impl<'a> Iterator for RopeStrings<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        loop {
            match self.stack.pop() {
                None => return None,
                Some(&Nil) => (),
                Some(&Leaf(ref s)) => return Some(&s),
                Some(&Branch(ref cat)) => {
                    self.stack.push(&cat.right);
                    self.stack.push(&cat.left);
                }
            }
        }
    }
}

/// Move iterator over the strings of a `Rope`.
pub struct RopeMoveStrings {
    stack: Vec<Node>,
}

impl Iterator for RopeMoveStrings {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        loop {
            match self.stack.pop() {
                None => return None,
                Some(Nil) => (),
                Some(Leaf(s)) => return Some(s),
                Some(Branch(cat)) => {
                    let cat = *cat;
                    self.stack.push(cat.right);
                    self.stack.push(cat.left);
                }
            }
        }
    }
}

/// Iterator over the strings of a `Rope`.
pub struct RopeSubstrings<'a> {
    start: usize,
    end: usize,
    stack: Vec<(usize, &'a Node)>,
}

impl<'a> RopeSubstrings<'a> {
    fn new(root: &Node, start: usize, end: usize) -> RopeSubstrings {
        RopeSubstrings { start: start, end: end, stack: vec![(0, root)] }
    }
}

impl<'a> Iterator for RopeSubstrings<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        loop {
            let (offset, node) = match self.stack.pop() {
                None => return None,
                Some(x) => x,
            };
            // Clamp start and end within the node's bounds
            let len = node.len();
            let start = if self.start < offset { 0 }
                        else { self.start - offset };
            let end = if self.end > offset + len { len }
                      else { self.end - offset };
            match *node {
                Nil => (),
                Leaf(ref s) => return Some(&s[start..end]),
                Branch(ref cat) => {
                    let left_len = cat.left.len();
                    if end > left_len {
                        self.stack.push((offset + left_len, &cat.right));
                    }
                    if start < left_len {
                        self.stack.push((offset, &cat.left));
                    }
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::Rope;

    #[test]
    fn test_append() {
        let mut rope = Rope::from_string("ab".to_string());
        rope.append_string("cd".to_string());
        assert!(&rope == "abcd");
    }

    #[test]
    fn test_prepend() {
        let mut rope = Rope::from_string("ab".to_string());
        rope.prepend_string("cd".to_string());
        assert!(&rope == "cdab");
    }

    #[test]
    fn test_split() {
        let rope = Rope::from_string("abcd".to_string());
        // Split nothing at the front
        let (left, rope) = rope.split(0);
        assert!(&left == "");
        assert!(&rope == "abcd");

        // Split nothing at the back
        let (rope, right) = rope.split(4);
        assert!(&rope == "abcd");
        assert!(&right == "");

        let (left, right) = rope.split(2);
        assert!(&left == "ab");
        assert!(&right == "cd");
    }

    #[test]
    fn test_insert() {
        let mut rope = Rope::from_string("ab".to_string());
        rope.insert_string(1, "cd".to_string());
        assert!(&rope == "acdb");
    }

    fn example_rope() -> Rope {
        let mut rope = Rope::from_string("cdef".to_string());
        rope.prepend_string("ab".to_string());
        rope.append_string("gh".to_string());
        rope
    }

    #[test]
    fn test_delete() {
        let mut rope = example_rope();
        // Delete nothing
        let deleted = rope.delete(0, 0);
        assert!(&rope == "abcdefgh");
        assert!(&deleted == "");

        let deleted = rope.delete(1, 3);
        assert!(&rope == "adefgh");
        assert!(&deleted == "bc");

        // Delete everything
        let deleted = rope.delete(0, 6);
        assert!(&rope == "");
        assert!(&deleted == "adefgh");
    }

    #[test]
    fn test_truncate() {
        let mut rope = example_rope();
        // Truncate nothing
        let (left, right) = rope.truncate(0, 8);
        assert!(&rope == "abcdefgh");
        assert!(&left == "");
        assert!(&right == "");

        let (left, right) = rope.truncate(1, 7);
        assert!(&rope == "bcdefg");
        assert!(&left == "a");
        assert!(&right == "h");

        // Truncate everything
        let (left, right) = rope.truncate(3, 3);
        assert!(&rope == "");
        assert!(&left == "bcd");
        assert!(&right == "efg");

    }

    #[test]
    fn test_substring() {
        let rope = example_rope();
        assert!(rope.substring(1, 7) == "bcdefg");

        // Empty substrings
        assert!(rope.substring(0, 0) == "");
        assert!(rope.substring(8, 8) == "");
        assert!(rope.substring(4, 4) == "");

        // Ensure slices are used when possible
        let sub = rope.substring(2, 6);
        assert!(sub.is_borrowed() && sub == "cdef");

        let sub = rope.substring(3, 5);
        assert!(sub.is_borrowed() && sub == "de");
    }

    #[test]
    fn test_strings_iter() {
        let rope = example_rope();
        assert_eq!(rope.strings().count(), 3);
        let expected = ["ab", "cdef", "gh"];
        assert!(rope.strings().zip(expected.iter()).all(|(a, &b)| a == b));
    }

    #[test]
    fn test_into_strings_iter() {
        let rope = example_rope();
        let strings: Vec<String> = rope.into_strings().collect();
        let expected = vec!["ab".to_string(), "cdef".to_string(),
            "gh".to_string()];
        assert_eq!(strings, expected);
    }

    #[test]
    fn test_cmp() {
        let mut rope1 = Rope::from_string("aa".to_string());
        let mut rope2 = Rope::from_string("aa".to_string());
        assert!(rope1 == rope2);
        assert!(rope1 <= rope2);

        rope2.append_string("a".to_string());
        assert!(rope1 < rope2);

        rope1.append_string("b".to_string());
        assert!(rope1 > rope2);

        rope2.prepend_string("b".to_string());
        assert!(rope1 < rope2);
    }
}
