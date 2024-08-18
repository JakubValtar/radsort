#![warn(clippy::all)]

#[test]
fn sort_bool() {
    let mut actual = [
        true, false, true, true, true, false, true, true, false, false, false
    ];
    let mut expected = actual;
    radsort::sort(&mut actual);
    expected.sort();
    assert_eq!(actual, expected);
}

#[test]
fn sort_char() {
    let mut actual = [
        '\u{0}',     '\u{1}',     '\u{F}',     '\u{7F}',    // 1-byte sequence
        '\u{80}',    '\u{81}',    '\u{FF}',    '\u{7FF}',   // 2-byte sequence
        '\u{800}',   '\u{801}',   '\u{FFF}',   '\u{FFFF}',  // 3-byte sequence
        '\u{10000}', '\u{10001}', '\u{FFFFF}', '\u{10FFFF}' // 4-byte sequence
    ];
    actual.reverse();
    let mut expected = actual.clone();
    radsort::sort(&mut actual);
    expected.sort();
    assert_eq!(actual, expected);
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn sort_integer() {
    macro_rules! implement {
        ($($t:ident)*) => ($(
            let mut actual = [
                std::$t::MIN, std::$t::MIN+1, std::$t::MIN / 2,
                std::$t::MAX, std::$t::MAX-1, std::$t::MAX / 2,
                -1i8 as $t, 0, 1,
            ];
            let mut expected = actual.clone();
            expected.sort();
            radsort::sort(&mut actual);
            assert_eq!(actual, expected);
        )*)
    }
    implement! {
        u8 u16 u32 u64 u128 usize
        i8 i16 i32 i64 i128 isize
    }
}

#[test]
fn sort_float() {
    macro_rules! implement {
        ($($t:ident)*) => ($(
            let mut actual = [
                0.0, -0.0, 1.0, -1.0,
                std::$t::MIN, std::$t::MAX,
                std::$t::MIN_POSITIVE, -std::$t::MIN_POSITIVE, 
                std::$t::EPSILON, -std::$t::EPSILON,
                std::$t::INFINITY, std::$t::NEG_INFINITY,
            ];
            let mut expected = actual.clone();
            expected.sort_by(|a, b| a.partial_cmp(b).unwrap());
            radsort::sort(&mut actual);
            assert_eq!(actual, expected);
        )*)
    }
    implement! { f32 f64 }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn sort_cached() {
    macro_rules! implement {
        ($($t:ident)*) => ($(
            let mut actual = [
                std::$t::MIN, std::$t::MIN+1, std::$t::MIN / 2,
                std::$t::MAX, std::$t::MAX-1, std::$t::MAX / 2,
                -1i8 as $t, 0, 1,
            ];
            let mut expected = actual.clone();
            expected.sort();
            radsort::sort_by_cached_key(&mut actual, |t| *t);
            assert_eq!(actual, expected);
        )*)
    }
    implement! {
        u8 u16 u32 u64 u128 usize
        i8 i16 i32 i64 i128 isize
    }
}

#[test]
fn sort_struct() {
    #[derive(PartialEq, Debug, Clone)]
    struct Data(u32);
    let source: Vec<_> = (0..512).map(Data).collect();
    
    {   // Sorting references
        let source_copy = source.clone();
        let mut actual: Vec<&Data> = source.iter().collect();
        let mut expected = actual.clone();
        radsort::sort_by_key(&mut actual, |d| d.0);
        expected.sort_by_key(|d| d.0);
        assert_eq!(actual, expected);
        assert_eq!(source, source_copy);
    }
    
    {   // Sorting actual values
        let mut actual = source.clone();
        let mut expected = source.clone();
        radsort::sort_by_key(&mut actual, |d| d.0);
        expected.sort_by_key(|d| d.0);
        assert_eq!(actual, expected);
    }
}

/// Test sorting by multiple keys in a tuple.
#[test]
fn sort_compound() {

    let mut actual = Vec::new();

    for a in 0..10 {
        for b in 0..10 {
            for c in 0..10 {
                for d in 0..10 {
                    actual.push([a, b, c, d]);
                }
            }
        }
    }
    
    actual.reverse();

    let mut expected = actual.clone();

    radsort::sort_by_key(&mut expected, |a| a[0]);
    radsort::sort_by_key(&mut actual, |a| (a[0],));
    assert_eq!(actual, expected);

    radsort::sort_by_key(&mut expected, |a| a[1]);
    radsort::sort_by_key(&mut expected, |a| a[0]);
    radsort::sort_by_key(&mut actual, |a| (a[0], a[1]));
    assert_eq!(actual, expected);

    radsort::sort_by_key(&mut expected, |a| a[2]);
    radsort::sort_by_key(&mut expected, |a| a[1]);
    radsort::sort_by_key(&mut expected, |a| a[0]);
    radsort::sort_by_key(&mut actual, |a| (a[0], a[1], a[2]));
    assert_eq!(actual, expected);

    radsort::sort_by_key(&mut expected, |a| a[3]);
    radsort::sort_by_key(&mut expected, |a| a[2]);
    radsort::sort_by_key(&mut expected, |a| a[1]);
    radsort::sort_by_key(&mut expected, |a| a[0]);
    radsort::sort_by_key(&mut actual, |a| (a[0], a[1], a[2], a[3]));
    assert_eq!(actual, expected);
}

#[test]
fn sort_zst() {
    let mut actual = [(); 10];
    let mut expected = actual.clone();
    expected.sort();
    radsort::sort_by_key(&mut actual, |_| 0);
    assert_eq!(actual, expected);
}

/// Tests that unreliable key function gets detected
#[test]
#[should_panic(expected = "The key function is not reliable: when called repeatedly, \
    it returned different keys for the same element.")]
fn unreliable_key_function() {

    let mut key_fn_call_count = 0;

    let mut data: Vec<u16> = (200..300).collect();

    radsort::sort_by_key(&mut data, |v| {
        key_fn_call_count += 1;
        if key_fn_call_count == 250 {
            !v // flip all the bits, changing the element bucket
        } else {
            *v
        }
    });
}

/// Tests that the slice is left in a consistent state after a panic.
#[test]
fn exception_safety() {
    
    // Crossing u8::MAX boundary to make sure that values differ in both bytes
    // and a digit won't be skipped.
    let mut actual: Vec<u16> = (200..300).collect();
    let expected = actual.clone();

    actual.reverse();
    
    let wrapper = std::panic::AssertUnwindSafe(&mut actual);

    std::panic::catch_unwind(move || {
        let mut key_fn_call_count = 0;
        radsort::sort_by_key(wrapper.0, |v| {
            key_fn_call_count += 1;
            if key_fn_call_count == 250 {
                // Second sorting pass, the slice is being written to
                panic!("panic in the key function");
            } else {
                *v
            }
        });
    }).expect_err("panic was not thrown");

    actual.sort();
    assert_eq!(expected, actual);
}
