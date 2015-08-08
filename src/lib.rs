// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A growable list type with heap-allocated contents, written `Vec<T>` but
//! pronounced 'vector.'
//!
//! Vectors have `O(1)` indexing, amortized `O(1)` push (to the end) and
//! `O(1)` pop (from the end).
//!
//! # Examples
//!
//! You can explicitly create a `Vec<T>` with `new()`:
//!
//! ```
//! let v: Vec<i32> = Vec::new();
//! ```
//!
//! ...or by using the `vec!` macro:
//!
//! ```
//! let v: Vec<i32> = vec![];
//!
//! let v = vec![1, 2, 3, 4, 5];
//!
//! let v = vec![0; 10]; // ten zeroes
//! ```
//!
//! You can `push` values onto the end of a vector (which will grow the vector as needed):
//!
//! ```
//! let mut v = vec![1, 2];
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! let mut v = vec![1, 2];
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the `Index` and `IndexMut` traits):
//!
//! ```
//! let mut v = vec![1, 2, 3];
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```

#![feature(unsafe_no_drop_flag, core, core_intrinsics)]
#![feature(rt, unsafe_no_drop_flag, unique, heap_api, box_raw, filling_drop)]
#![cfg_attr(test, feature(test))]

extern crate core;
pub mod raw_vec;

#[cfg(test)]
mod bench;

use core::intrinsics::{arith_offset, assume, drop_in_place};
use core::iter::FromIterator;
use core::mem;
use core::ops::{Index, IndexMut, Deref};
use core::ops;
use core::ptr;
use core::slice;

use raw_vec::RawVec;

/// A growable list type, written `Vec<T>` but pronounced 'vector.'
///
/// # Examples
///
/// ```
/// let mut vec = Vec::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3].iter().cloned());
///
/// for x in &vec {
///     println!("{}", x);
/// }
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
///
/// The `vec!` macro is provided to make initialization more convenient:
///
/// ```
/// let mut vec = vec![1, 2, 3];
/// vec.push(4);
/// assert_eq!(vec, [1, 2, 3, 4]);
/// ```
///
/// It can also initialize each element of a `Vec<T>` with a given value:
///
/// ```
/// let vec = vec![0; 5];
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
/// ```
///
/// Use a `Vec<T>` as an efficient stack:
///
/// ```
/// let mut stack = Vec::new();
///
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
///
/// while let Some(top) = stack.pop() {
///     // Prints 3, 2, 1
///     println!("{}", top);
/// }
/// ```
///
/// # Capacity and reallocation
///
/// The capacity of a vector is the amount of space allocated for any future
/// elements that will be added onto the vector. This is not to be confused with
/// the *length* of a vector, which specifies the number of actual elements
/// within the vector. If a vector's length exceeds its capacity, its capacity
/// will automatically be increased, but its elements will have to be
/// reallocated.
///
/// For example, a vector with capacity 10 and length 0 would be an empty vector
/// with space for 10 more elements. Pushing 10 or fewer elements onto the
/// vector will not change its capacity or cause reallocation to occur. However,
/// if the vector's length is increased to 11, it will have to reallocate, which
/// can be slow. For this reason, it is recommended to use `Vec::with_capacity`
/// whenever possible to specify how big the vector is expected to get.
#[unsafe_no_drop_flag]
pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

////////////////////////////////////////////////////////////////////////////////
// Inherent methods
////////////////////////////////////////////////////////////////////////////////

impl<T> Vec<T> {
    /// Constructs a new, empty `Vec<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec: Vec<i32> = Vec::new();
    /// ```
    #[inline]
        pub fn new() -> Vec<T> {
        Vec { buf: RawVec::new(), len: 0 }
    }

    /// Constructs a new, empty `Vec<T>` with the specified capacity.
    ///
    /// The vector will be able to hold exactly `capacity` elements without reallocating. If
    /// `capacity` is 0, the vector will not allocate.
    ///
    /// It is important to note that this function does not specify the *length* of the returned
    /// vector, but only the *capacity*. (For an explanation of the difference between length and
    /// capacity, see the main `Vec<T>` docs above, 'Capacity and reallocation'.)
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// ```
    #[inline]
        pub fn with_capacity(capacity: usize) -> Vec<T> {
        Vec { buf: RawVec::with_capacity(capacity), len: 0 }
    }

    /// Creates a `Vec<T>` directly from the raw components of another vector.
    ///
    /// # Unsafety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` needs to have been previously allocated via `String`/`Vec<T>`
    ///   (at least, it's highly likely to be incorrect if it wasn't).
    /// * `length` needs to be the length that less than or equal to `capacity`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal datastructures.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr;
    /// use std::mem;
    ///
    /// fn main() {
    ///     let mut v = vec![1, 2, 3];
    ///
    ///     // Pull out the various important pieces of information about `v`
    ///     let p = v.as_mut_ptr();
    ///     let len = v.len();
    ///     let cap = v.capacity();
    ///
    ///     unsafe {
    ///         // Cast `v` into the void: no destructor run, so we are in
    ///         // complete control of the allocation to which `p` points.
    ///         mem::forget(v);
    ///
    ///         // Overwrite memory with 4, 5, 6
    ///         for i in 0..len as isize {
    ///             ptr::write(p.offset(i), 4 + i);
    ///         }
    ///
    ///         // Put everything back together into a Vec
    ///         let rebuilt = Vec::from_raw_parts(p, len, cap);
    ///         assert_eq!(rebuilt, [4, 5, 6]);
    ///     }
    /// }
    /// ```
        pub unsafe fn from_raw_parts(ptr: *mut T, length: usize,
                                 capacity: usize) -> Vec<T> {
        Vec {
            buf: RawVec::from_raw_parts(ptr, capacity),
            len: length,
        }
    }

    /// Creates a vector by copying the elements from a raw pointer.
    ///
    /// This function will copy `elts` contiguous elements starting at `ptr`
    /// into a new allocation owned by the returned `Vec<T>`. The elements of
    /// the buffer are copied into the vector without cloning, as if
    /// `ptr::read()` were called on them.
    #[inline]


    pub unsafe fn from_raw_buf(ptr: *const T, elts: usize) -> Vec<T> {
        let mut dst = Vec::with_capacity(elts);
        dst.set_len(elts);
        ptr::copy_nonoverlapping(ptr, dst.as_mut_ptr(), elts);
        dst
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec: Vec<i32> = Vec::with_capacity(10);
    /// assert_eq!(vec.capacity(), 10);
    /// ```
    #[inline]
        pub fn capacity(&self) -> usize {
        self.buf.cap()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
        pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(self.len, additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `Vec<T>`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.reserve_exact(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
        pub fn reserve_exact(&mut self, additional: usize) {
        self.buf.reserve_exact(self.len, additional);
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() >= 3);
    /// ```
        pub fn shrink_to_fit(&mut self) {
        self.buf.shrink_to_fit(self.len);
    }

    /// Converts the vector into Box<[T]>.
    ///
    /// Note that this will drop any excess capacity. Calling this and
    /// converting back to a vector with `into_vec()` is equivalent to calling
    /// `shrink_to_fit()`.
        pub fn into_boxed_slice(mut self) -> Box<[T]> {
        unsafe {
            self.shrink_to_fit();
            let buf = ptr::read(&self.buf);
            mem::forget(self);
            buf.into_box()
        }
    }

    /// Shorten a vector, dropping excess elements.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.truncate(2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
        pub fn truncate(&mut self, len: usize) {
        unsafe {
            // drop any extra elements
            while len < self.len {
                // decrement len before the read(), so a panic on Drop doesn't
                // re-drop the just-failed value.
                self.len -= 1;
                ptr::read(self.get_unchecked(self.len));
            }
        }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    #[inline]

    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    #[inline]

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self[..]
    }

    /// Sets the length of a vector.
    ///
    /// This will explicitly set the size of the vector, without actually
    /// modifying its buffers, so it is up to the caller to ensure that the
    /// vector is actually the specified size.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3, 4];
    /// unsafe {
    ///     v.set_len(1);
    /// }
    /// ```
    #[inline]
        pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// Removes an element from anywhere in the vector and return it, replacing
    /// it with the last element.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[inline]
        pub fn swap_remove(&mut self, index: usize) -> T {
        let length = self.len();
        self.swap(index, length - 1);
        self.pop().unwrap()
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after position `i` one position to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than the vector's length.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// vec.insert(1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
        pub fn insert(&mut self, index: usize, element: T) {
        let len = self.len();
        assert!(index <= len);

        // space for the new element
        if len == self.buf.cap() { self.buf.double(); }

        unsafe { // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().offset(index as isize);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after position `index` one position to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3];
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, [1, 3]);
    /// ```
        pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len);
        unsafe { // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().offset(index as isize);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain(|&x| x%2 == 0);
    /// assert_eq!(vec, [2, 4]);
    /// ```
        pub fn retain<F>(&mut self, mut f: F) where F: FnMut(&T) -> bool {
        let len = self.len();
        let mut del = 0;
        {
            let v = &mut **self;

            for i in 0..len {
                if !f(&v[i]) {
                    del += 1;
                } else if del > 0 {
                    v.swap(i-del, i);
                }
            }
        }
        if del > 0 {
            self.truncate(len - del);
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
        pub fn push(&mut self, value: T) {
        // This will panic or abort if we would allocate > isize::MAX bytes
        // or if the length increment would overflow for zero-sized types.
        if self.len() == self.capacity() { self.buf.double(); }
        unsafe {
            let end = self.as_mut_ptr().offset(self.len as isize);
            ptr::write(end, value);
            self.len += 1;
        }
    }

    /// Removes the last element from a vector and returns it, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    #[inline]
        pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                Some(ptr::read(self.get_unchecked(self.len())))
            }
        }
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(append)]
    ///
    /// let mut vec = vec![1, 2, 3];
    /// let mut vec2 = vec![4, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2, []);
    /// ```
    #[inline]

    pub fn append(&mut self, other: &mut Self) {
        self.reserve(other.len());
        let len = self.len();
        unsafe {
            ptr::copy_nonoverlapping(
                other.as_ptr(),
                self.get_unchecked_mut(len),
                other.len());
        }

        self.len += other.len();
        unsafe { other.set_len(0); }
    }



    /// Clears the vector, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    #[inline]
        pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = vec![1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
        pub fn len(&self) -> usize { self.len }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = Vec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
        pub fn is_empty(&self) -> bool { self.len() == 0 }



    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated `Self`. `self` contains elements `[0, at)`,
    /// and the returned `Self` contains elements `[at, len)`.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(split_off)]
    ///
    /// let mut vec = vec![1,2,3];
    /// let vec2 = vec.split_off(1);
    /// assert_eq!(vec, [1]);
    /// assert_eq!(vec2, [2, 3]);
    /// ```
    #[inline]

    pub fn split_off(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "`at` out of bounds");

        let other_len = self.len - at;
        let mut other = Vec::with_capacity(other_len);

        // Unsafely `set_len` and copy items to `other`.
        unsafe {
            self.set_len(at);
            other.set_len(other_len);

            ptr::copy_nonoverlapping(
                self.as_ptr().offset(at as isize),
                other.as_mut_ptr(),
                other.len());
        }
        other
    }

}

impl<T: Clone> Vec<T> {
    /// Resizes the `Vec` in-place so that `len()` is equal to `new_len`.
    ///
    /// Calls either `extend()` or `truncate()` depending on whether `new_len`
    /// is larger than the current value of `len()` or not.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_resize)]
    ///
    /// let mut vec = vec!["hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(vec, ["hello", "world", "world"]);
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.resize(2, 0);
    /// assert_eq!(vec, [1, 2]);
    /// ```

    pub fn resize(&mut self, new_len: usize, value: T) {
        let len = self.len();

        if new_len > len {
            self.extend_with_element(new_len - len, value);
        } else {
            self.truncate(new_len);
        }
    }

    /// Extend the vector by `n` additional clones of `value`.
    fn extend_with_element(&mut self, n: usize, value: T) {
        self.reserve(n);

        unsafe {
            let len = self.len();
            let mut ptr = self.as_mut_ptr().offset(len as isize);
            // Write all elements except the last one
            for i in 1..n {
                ptr::write(ptr, value.clone());
                ptr = ptr.offset(1);
                // Increment the length in every step in case clone() panics
                self.set_len(len + i);
            }

            if n > 0 {
                // We can write the last element directly without cloning needlessly
                ptr::write(ptr, value);
                self.set_len(len + n);
            }
        }
    }

    /// Appends all elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `Vec`. The `other` vector is traversed in-order.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_push_all)]
    ///
    /// let mut vec = vec![1];
    /// vec.push_all(&[2, 3, 4]);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    #[inline]

    pub fn push_all(&mut self, other: &[T]) {
        self.reserve(other.len());

        for i in 0..other.len() {
            let len = self.len();

            // Unsafe code so this can be optimised to a memcpy (or something similarly
            // fast) when T is Copy. LLVM is easily confused, so any extra operations
            // during the loop can prevent this optimisation.
            unsafe {
                ptr::write(
                    self.get_unchecked_mut(len),
                    other.get_unchecked(i).clone());
                self.set_len(len + 1);
            }
        }
    }
}

impl<T: PartialEq> Vec<T> {
    /// Removes consecutive repeated elements in the vector.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 2, 3, 2];
    ///
    /// vec.dedup();
    ///
    /// assert_eq!(vec, [1, 2, 3, 2]);
    /// ```
        pub fn dedup(&mut self) {
        unsafe {
            // Although we have a mutable reference to `self`, we cannot make
            // *arbitrary* changes. The `PartialEq` comparisons could panic, so we
            // must ensure that the vector is in a valid state at all time.
            //
            // The way that we handle this is by using swaps; we iterate
            // over all the elements, swapping as we go so that at the end
            // the elements we wish to keep are in the front, and those we
            // wish to reject are at the back. We can then truncate the
            // vector. This operation is still O(n).
            //
            // Example: We start in this state, where `r` represents "next
            // read" and `w` represents "next_write`.
            //
            //           r
            //     +---+---+---+---+---+---+
            //     | 0 | 1 | 1 | 2 | 3 | 3 |
            //     +---+---+---+---+---+---+
            //           w
            //
            // Comparing self[r] against self[w-1], this is not a duplicate, so
            // we swap self[r] and self[w] (no effect as r==w) and then increment both
            // r and w, leaving us with:
            //
            //               r
            //     +---+---+---+---+---+---+
            //     | 0 | 1 | 1 | 2 | 3 | 3 |
            //     +---+---+---+---+---+---+
            //               w
            //
            // Comparing self[r] against self[w-1], this value is a duplicate,
            // so we increment `r` but leave everything else unchanged:
            //
            //                   r
            //     +---+---+---+---+---+---+
            //     | 0 | 1 | 1 | 2 | 3 | 3 |
            //     +---+---+---+---+---+---+
            //               w
            //
            // Comparing self[r] against self[w-1], this is not a duplicate,
            // so swap self[r] and self[w] and advance r and w:
            //
            //                       r
            //     +---+---+---+---+---+---+
            //     | 0 | 1 | 2 | 1 | 3 | 3 |
            //     +---+---+---+---+---+---+
            //                   w
            //
            // Not a duplicate, repeat:
            //
            //                           r
            //     +---+---+---+---+---+---+
            //     | 0 | 1 | 2 | 3 | 1 | 3 |
            //     +---+---+---+---+---+---+
            //                       w
            //
            // Duplicate, advance r. End of vec. Truncate to w.

            let ln = self.len();
            if ln <= 1 { return; }

            // Avoid bounds checks by using raw pointers.
            let p = self.as_mut_ptr();
            let mut r: usize = 1;
            let mut w: usize = 1;

            while r < ln {
                let p_r = p.offset(r as isize);
                let p_wm1 = p.offset((w - 1) as isize);
                if *p_r != *p_wm1 {
                    if r != w {
                        let p_w = p_wm1.offset(1);
                        mem::swap(&mut *p_r, &mut *p_w);
                    }
                    w += 1;
                }
                r += 1;
            }

            self.truncate(w);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Internal methods and functions
////////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
    let mut v = Vec::with_capacity(n);
    v.extend_with_element(n, elem);
    v
}

impl<T> Index<usize> for Vec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        // NB built-in indexing via `&[T]`
        &(**self)[index]
    }
}

impl<T> IndexMut<usize> for Vec<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        // NB built-in indexing via `&mut [T]`
        &mut (**self)[index]
    }
}


impl<T> ops::Index<ops::Range<usize>> for Vec<T> {
    type Output = [T];

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &[T] {
        Index::index(&**self, index)
    }
}
impl<T> ops::Index<ops::RangeTo<usize>> for Vec<T> {
    type Output = [T];

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &[T] {
        Index::index(&**self, index)
    }
}
impl<T> ops::Index<ops::RangeFrom<usize>> for Vec<T> {
    type Output = [T];

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &[T] {
        Index::index(&**self, index)
    }
}
impl<T> ops::Index<ops::RangeFull> for Vec<T> {
    type Output = [T];

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &[T] {
        self
    }
}

impl<T> ops::IndexMut<ops::Range<usize>> for Vec<T> {

    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut [T] {
        IndexMut::index_mut(&mut **self, index)
    }
}
impl<T> ops::IndexMut<ops::RangeTo<usize>> for Vec<T> {

    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut [T] {
        IndexMut::index_mut(&mut **self, index)
    }
}
impl<T> ops::IndexMut<ops::RangeFrom<usize>> for Vec<T> {

    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut [T] {
        IndexMut::index_mut(&mut **self, index)
    }
}
impl<T> ops::IndexMut<ops::RangeFull> for Vec<T> {

    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut [T] {
        self
    }
}

impl<T> ops::Deref for Vec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe {
            let p = self.buf.ptr();
            assume(p != 0 as *mut T);
            slice::from_raw_parts(p, self.len)
        }
    }
}

impl<T> ops::DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe {
            let ptr = self.buf.ptr();
            assume(!ptr.is_null());
            slice::from_raw_parts_mut(ptr, self.len)
        }
    }
}

impl<T> FromIterator<T> for Vec<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item=T>>(iterable: I) -> Vec<T> {
        // Unroll the first iteration, as the vector is going to be
        // expanded on this iteration in every case when the iterable is not
        // empty, but the loop in extend_desugared() is not going to see the
        // vector being full in the few subsequent loop iterations.
        // So we get better branch prediction and the possibility to
        // construct the vector with initial estimated capacity.
        let mut iterator = iterable.into_iter();
        let mut vector = match iterator.next() {
            None => return Vec::new(),
            Some(element) => {
                let (lower, _) = iterator.size_hint();
                let mut vector = Vec::with_capacity(lower.saturating_add(1));
                unsafe {
                    ptr::write(vector.get_unchecked_mut(0), element);
                    vector.set_len(1);
                }
                vector
            }
        };
        vector.extend_desugared(iterator);
        vector
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the vector (from start to end). The vector cannot be used after calling
    /// this.
    ///
    /// # Examples
    ///
    /// ```
    /// let v = vec!["a".to_string(), "b".to_string()];
    /// for s in v.into_iter() {
    ///     // s has type String, not &String
    ///     println!("{}", s);
    /// }
    /// ```
    #[inline]
    fn into_iter(mut self) -> IntoIter<T> {
        unsafe {
            let ptr = self.as_mut_ptr();
            assume(!ptr.is_null());
            let begin = ptr as *const T;
            let end = if mem::size_of::<T>() == 0 {
                arith_offset(ptr as *const i8, self.len() as isize) as *const T
            } else {
                ptr.offset(self.len() as isize) as *const T
            };
            let buf = ptr::read(&self.buf);
            mem::forget(self);
            IntoIter { buf: buf, ptr: begin, end: end }
        }
    }
}

impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Vec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(mut self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T> Extend<T> for Vec<T> {
    #[inline]
    fn extend<I: IntoIterator<Item=T>>(&mut self, iterable: I) {
        self.extend_desugared(iterable.into_iter())
    }
}

impl<T> Vec<T> {
    fn extend_desugared<I: Iterator<Item=T>>(&mut self, mut iterator: I) {
        // This function should be the moral equivalent of:
        //
        //      for item in iterator {
        //          self.push(item);
        //      }
        while let Some(element) = iterator.next() {
            let len = self.len();
            if len == self.capacity() {
                let (lower, _) = iterator.size_hint();
                self.reserve(lower.saturating_add(1));
            }
            unsafe {
                ptr::write(self.get_unchecked_mut(len), element);
                // NB can't overflow since we would have had to alloc the address space
                self.set_len(len + 1);
            }
        }
    }
}

impl<'a, T: 'a + Copy> Extend<&'a T> for Vec<T> {
    fn extend<I: IntoIterator<Item=&'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        // NOTE: this is currently abusing the fact that ZSTs can't impl Drop.
        // Or rather, that impl'ing Drop makes them not zero-sized. This is
        // OK because exactly when this stops being a valid assumption, we
        // don't need unsafe_no_drop_flag shenanigans anymore.
        if self.buf.unsafe_no_drop_flag_needs_drop() {
            for x in self.iter_mut() {
                unsafe { drop_in_place(x); }
            }
        }
        // RawVec handles deallocation
    }
}

////////////////////////////////////////////////////////////////////////////////
// Iterators
////////////////////////////////////////////////////////////////////////////////

/// An iterator that moves out of a vector.
pub struct IntoIter<T> {
    buf: RawVec<T>,
    ptr: *const T,
    end: *const T
}

unsafe impl<T: Send> Send for IntoIter<T> { }
unsafe impl<T: Sync> Sync for IntoIter<T> { }

impl<T> IntoIter<T> {
    #[inline]
    /// Drops all items that have not yet been moved and returns the empty vector.
    pub fn into_inner(mut self) -> Vec<T> {
        unsafe {
            for _x in self.by_ref() { }
            let buf = ptr::read(&self.buf);
            mem::forget(self);
            Vec { buf: buf, len: 0 }
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        unsafe {
            if self.ptr == self.end {
                None
            } else {
                if mem::size_of::<T>() == 0 {
                    // purposefully don't use 'ptr.offset' because for
                    // vectors with 0-size elements this would return the
                    // same pointer.
                    self.ptr = arith_offset(self.ptr as *const i8, 1) as *const T;

                    // Use a non-null pointer value
                    Some(ptr::read(1 as *mut T))
                } else {
                    let old = self.ptr;
                    self.ptr = self.ptr.offset(1);

                    Some(ptr::read(old))
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let diff = (self.end as usize) - (self.ptr as usize);
        let size = mem::size_of::<T>();
        let exact = diff / (if size == 0 {1} else {size});
        (exact, Some(exact))
    }

    #[inline]
    fn count(self) -> usize {
        self.size_hint().0
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        unsafe {
            if self.end == self.ptr {
                None
            } else {
                if mem::size_of::<T>() == 0 {
                    // See above for why 'ptr.offset' isn't used
                    self.end = arith_offset(self.end as *const i8, -1) as *const T;

                    // Use a non-null pointer value
                    Some(ptr::read(1 as *mut T))
                } else {
                    self.end = self.end.offset(-1);

                    Some(ptr::read(mem::transmute(self.end)))
                }
            }
        }
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        // destroy the remaining elements
        for _x in self.by_ref() {}

        // RawVec handles deallocation
    }
}

/// A draining iterator for `Vec<T>`.
pub struct Drain<'a, T: 'a> {
    /// Index of tail to preserve
    tail_start: usize,
    /// Length of tail
    tail_len: usize,
    /// Current remaining range to remove
    iter: slice::IterMut<'a, T>,
    vec: *mut Vec<T>,
}

unsafe impl<'a, T: Sync> Sync for Drain<'a, T> {}
unsafe impl<'a, T: Send> Send for Drain<'a, T> {}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|elt|
            unsafe {
                ptr::read(elt as *const _)
            }
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|elt|
            unsafe {
                ptr::read(elt as *const _)
            }
        )
    }
}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        // exhaust self first
        while let Some(_) = self.next() { }

        if self.tail_len > 0 {
            unsafe {
                let source_vec = &mut *self.vec;
                // memmove back untouched tail, update to new length
                let start = source_vec.len();
                let tail = self.tail_start;
                let src = source_vec.as_ptr().offset(tail as isize);
                let dst = source_vec.as_mut_ptr().offset(start as isize);
                ptr::copy(src, dst, self.tail_len);
                source_vec.set_len(start + self.tail_len);
            }
        }
    }
}


impl<'a, T> ExactSizeIterator for Drain<'a, T> {}
