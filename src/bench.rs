extern crate test;

use std::collections::VecDeque;
use super::Vec;
use std;

const AMT1: usize = 1000;
const AMT2: usize = 1001;
const E1: u8 = 0;
const E2: u8 = 2;

#[bench]
fn macro_repeat1(b: &mut test::Bencher) {
    b.iter(|| { vec![E1; AMT1] });
}
#[bench]
fn macro_repeat2(b: &mut test::Bencher) {
    b.iter(|| { vec![E2; AMT2] });
}

#[bench]
fn map_clone1(b: &mut test::Bencher) {
    b.iter(|| {
        (0..AMT1).map(|_| E1).collect::<Vec<_>>()
    });
}
#[bench]
fn map_clone2(b: &mut test::Bencher) {
    b.iter(|| {
        (0..AMT2).map(|_| E2).collect::<Vec<_>>()
    });
}

#[bench]
fn repeat1(b: &mut test::Bencher) {
    b.iter(|| {
        std::iter::repeat(E1).take(AMT1).collect::<Vec<_>>()
    });
}
#[bench]
fn repeat2(b: &mut test::Bencher) {
    b.iter(|| {
        std::iter::repeat(E2).take(AMT2).collect::<Vec<_>>()
    });
}

#[bench]
fn skip_take1(b: &mut test::Bencher) {
    b.iter(|| {
        (E1..).skip(10).take(AMT1).collect::<Vec<_>>()
    });
}
#[bench]
fn skip_take2(b: &mut test::Bencher) {
    b.iter(|| {
        (E2..).skip(10).take(AMT2).collect::<Vec<_>>()
    });
}

#[bench]
fn take_skip1(b: &mut test::Bencher) {
    b.iter(|| {
        (E1..).take(AMT1 + 10).skip(10).collect::<Vec<_>>()
    });
}
#[bench]
fn take_skip2(b: &mut test::Bencher) {
    b.iter(|| {
        (E2..).take(AMT2 + 10).skip(10).collect::<Vec<_>>()
    });
}

#[bench]
fn push_all1(b: &mut test::Bencher) {
    let foo = vec![E1; AMT1];
    b.iter(|| {
        let mut v = Vec::new();
        v.push_all(&foo);
        v
    });
}
#[bench]
fn push_all2(b: &mut test::Bencher) {
    let foo = vec![E2; AMT2];
    b.iter(|| {
        let mut v = Vec::new();
        v.push_all(&foo);
        v
    });
}

#[bench]
fn push1(b: &mut test::Bencher) {
    let foo = vec![E1; AMT1];
    b.iter(|| {
        let mut v = Vec::new();
        v.reserve(foo.len());
        for &e in &foo {
            v.push(e);
        }
        v
    });
}
#[bench]
fn push2(b: &mut test::Bencher) {
    let foo = vec![E2; AMT2];
    b.iter(|| {
        let mut v = Vec::new();
        v.reserve(foo.len());
        for &e in &foo {
            v.push(e);
        }
        v
    });
}

#[bench]
fn push_split1(b: &mut test::Bencher) {
    let foo = vec![E1; AMT1];
    b.iter(|| {
        let mut v = Vec::new();
        let len = foo.len();
        v.reserve(len);
        let mut iter = foo.iter();
        for _ in 0..len {
            let e = iter.next().unwrap();
            v.push(e);
        }
        for e in iter {
            v.push(e);
        }
        v
    });
}
#[bench]
fn push_split2(b: &mut test::Bencher) {
    let foo = vec![E2; AMT2];
    b.iter(|| {
        let mut v = Vec::new();
        let len = foo.len();
        v.reserve(len);
        let mut iter = foo.iter();
        for _ in 0..len {
            let e = iter.next().unwrap();
            v.push(e);
        }
        for e in iter {
            v.push(e);
        }
        v
    });
}

#[bench]
fn push_assume1(b: &mut test::Bencher) {
    let foo = vec![E1; AMT1];
    b.iter(|| {
        let mut v = Vec::new();
        v.reserve(foo.len());
        for &e in &foo {
            unsafe { ::std::intrinsics::assume(v.capacity() != v.len()) }
            v.push(e);
        }
        v
    });
}
#[bench]
fn push_assume2(b: &mut test::Bencher) {
    let foo = vec![E2; AMT2];
    b.iter(|| {
        let mut v = Vec::new();
        v.reserve(foo.len());
        for &e in &foo {
            unsafe { ::std::intrinsics::assume(v.capacity() != v.len()) }
            v.push(e);
        }
        v
    });
}

#[bench]
fn push_unsafe1(b: &mut test::Bencher) {
    use std::intrinsics::unreachable;
    use std::ptr;

    let foo = vec![E2; AMT2];
    b.iter(|| unsafe {
        let mut v = Vec::new();
        let len = foo.len();
        let old_len = v.len();
        v.reserve(len);
        let mut iter = foo.iter();

        for i in 0..len {
            let e = *iter.next().unwrap_or_else(|| unreachable());
            let end = v.as_mut_ptr().offset((old_len + i) as isize);
            ptr::write(end, e);
        }

        v.set_len(old_len + len);

        v
    });
}

#[bench]
fn push_unsafe2(b: &mut test::Bencher) {
    use std::intrinsics::unreachable;
    use std::ptr;

    let foo = vec![E2; AMT2];
    b.iter(|| unsafe {
        let mut v = Vec::new();
        let len = foo.len();
        let old_len = v.len();
        v.reserve(len);
        let mut iter = foo.iter();

        for i in 0..len {
            let e = *iter.next().unwrap_or_else(|| unreachable());
            let end = v.as_mut_ptr().offset((old_len + i) as isize);
            ptr::write(end, e);
            v.set_len(old_len + len);
        }

        v
    });
}

#[bench]
fn push_unsafe3(b: &mut test::Bencher) {
    use std::ptr;

    let foo = vec![E2; AMT2];
    b.iter(|| unsafe {
        let mut v = Vec::new();
        let len = foo.len();
        let old_len = v.len();
        v.reserve(len);
        let mut end = v.as_mut_ptr().offset(old_len as isize);

        for &e in &foo {
            ptr::write(end, e);
            end = end.offset(1);
        }

        v.set_len(old_len + len);

        v
    });
}

#[bench]
fn push_unsafe4(b: &mut test::Bencher) {
    use std::ptr;

    let foo = vec![E2; AMT2];
    b.iter(|| unsafe {
        let mut v = Vec::new();
        let len = foo.len();
        let old_len = v.len();
        v.reserve(len);
        let mut end = v.as_mut_ptr().offset(old_len as isize);

        for &e in &foo {
            ptr::write(end, e);
            end = end.offset(1);
            v.set_len(old_len + len);
        }

        v
    });
}

#[bench]
fn extend1(b: &mut test::Bencher) {
    let foo = vec![E1; AMT1];
    b.iter(|| {
        let mut v = Vec::new();
        v.extend(foo.iter().cloned());
        v
    });
}
#[bench]
fn extend2(b: &mut test::Bencher) {
    let foo = vec![E2; AMT2];
    b.iter(|| {
        let mut v = Vec::new();
        v.extend(foo.iter().cloned());
        v
    });
}
#[bench]
fn extend_vecdeque1(b: &mut test::Bencher) {
    let foo: VecDeque<u8> = vec![E1; AMT1].into_iter().collect();
    b.iter(|| {
        let mut v = Vec::new();
        v.extend(foo.iter().cloned());
        v
    });
}
#[bench]
fn extend_vecdeque2(b: &mut test::Bencher) {
    let foo: VecDeque<u8> = vec![E2; AMT2].into_iter().collect();
    b.iter(|| {
        let mut v = Vec::new();
        v.extend(foo.iter().cloned());
        v
    });
}
