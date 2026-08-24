#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::{convert::FromSpecImpl, range::spec_range_inclusive_new};

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

use core::ops::{Bound, RangeBounds, RangeInclusive};

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn range_cardinality(start: u64, end: u64) -> int {
    if start > end { 0 } else { end as int - start as int + 1 }
}
}

macro_rules! verified_const_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($args:tt)*) -> [$result:ident: $ret:ty]
        ensures [$($ensures:tt)*]
        $body:block
    ) => {
        #[cfg(not(verus_keep_ghost))]
        $(#[$meta])*
        $vis const fn $name($($args)*) -> $ret $body

        #[cfg(verus_keep_ghost)]
        verus! {
        $(#[$meta])*
        $vis fn $name($($args)*) -> ($result: $ret)
            ensures $($ensures)*,
            $body
        }
    };
}

macro_rules! verified_const_method {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($args:tt)*) -> [$result:ident: $ret:ty]
        ensures [$($ensures:tt)*]
        $body:block
    ) => {
        #[cfg(not(verus_keep_ghost))]
        $(#[$meta])*
        $vis const fn $name($($args)*) -> $ret $body

        #[cfg(verus_keep_ghost)]
        verus_impl! {
        $(#[$meta])*
        $vis fn $name($($args)*) -> ($result: $ret)
            ensures $($ensures)*,
            $body
        }
    };
}

macro_rules! verified_method {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($args:tt)*) -> [$result:ident: $ret:ty]
        ensures [$($ensures:tt)*]
        $body:block
    ) => {
        #[cfg(not(verus_keep_ghost))]
        $(#[$meta])*
        $vis fn $name($($args)*) -> $ret $body

        #[cfg(verus_keep_ghost)]
        verus_impl! {
        $(#[$meta])*
        $vis fn $name($($args)*) -> ($result: $ret)
            ensures $($ensures)*,
            $body
        }
    };
}

macro_rules! verified_from_std_range {
    ($value:ident, $body:block) => {
        #[cfg(not(verus_keep_ghost))]
        impl From<RangeInclusive<u64>> for SegmentRangeInclusive {
            fn from($value: RangeInclusive<u64>) -> Self $body
        }

        #[cfg(verus_keep_ghost)]
        verus! {
        impl From<RangeInclusive<u64>> for SegmentRangeInclusive {
            fn from($value: RangeInclusive<u64>) -> (result: SegmentRangeInclusive)
                ensures
                    !$value@.exhausted ==> result.start_spec() == $value@.start,
                    !$value@.exhausted ==> result.end_spec() == $value@.end,
                $body
        }
        }
    };
}

macro_rules! verified_to_std_range {
    ($source:ty, $value:ident, $body:block) => {
        #[cfg(not(verus_keep_ghost))]
        impl From<$source> for RangeInclusive<u64> {
            fn from($value: $source) -> Self $body
        }

        #[cfg(verus_keep_ghost)]
        verus! {
        impl From<$source> for RangeInclusive<u64> {
            fn from($value: $source) -> (result: RangeInclusive<u64>)
                ensures
                    result@.start == $value.start_spec(),
                    result@.end == $value.end_spec(),
                    !result@.exhausted,
                $body
        }
        }
    };
}

verified_const_fn! {
    pub(crate) fn range_is_empty(start: u64, end: u64) -> [result: bool]
    ensures [result == (start > end)]
    { start > end }
}

verified_const_fn! {
    pub(crate) fn range_contains(start: u64, end: u64, number: u64) -> [result: bool]
    ensures [result == (start <= end && start <= number && number <= end)]
    { !range_is_empty(start, end) && start <= number && number <= end }
}

verified_const_fn! {
    pub(crate) fn range_len(start: u64, end: u64) -> [result: u64]
    ensures [
        start > end ==> result == 0,
        start <= end && start == 0 && end == u64::MAX ==> result == u64::MAX,
        start <= end && !(start == 0 && end == u64::MAX)
            ==> result as int == range_cardinality(start, end) && result >= 1
    ]
    {
        if range_is_empty(start, end) {
            0
        } else if start == 0 && end == u64::MAX {
            u64::MAX
        } else {
            end - start + 1
        }
    }
}

/// Helper type to handle segment transaction and block INCLUSIVE ranges.
///
/// They can be modified on a hot loop, which makes the `std::ops::RangeInclusive` a poor fit.
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize, Eq, PartialEq, Hash, Clone, Copy)]
pub struct SegmentRangeInclusive {
    pub(super) start: u64,
    pub(super) end: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
#[derive(Clone, Copy)]
pub struct SegmentRangeInclusive {
    pub start: u64,
    pub end: u64,
}

impl SegmentRangeInclusive {
    pub open spec fn start_spec(&self) -> u64 {
        self.start
    }

    pub open spec fn end_spec(&self) -> u64 {
        self.end
    }
}
}

impl SegmentRangeInclusive {
    verified_const_method! {
        /// Creates a new [`SegmentRangeInclusive`].
        pub fn new(start: u64, end: u64) -> [result: Self]
        ensures [result.start_spec() == start, result.end_spec() == end]
        { Self { start, end } }
    }

    verified_const_method! {
        /// Start of the inclusive range.
        pub fn start(&self) -> [result: u64]
        ensures [result == self.start_spec()]
        { self.start }
    }

    verified_const_method! {
        /// End of the inclusive range.
        pub fn end(&self) -> [result: u64]
        ensures [result == self.end_spec()]
        { self.end }
    }

    verified_const_method! {
        /// Returns the length of the inclusive range.
        pub fn len(&self) -> [result: u64]
        ensures [
            self.start_spec() > self.end_spec() ==> result == 0,
            self.start_spec() <= self.end_spec()
                && self.start_spec() == 0 && self.end_spec() == u64::MAX
                ==> result == u64::MAX,
            self.start_spec() <= self.end_spec()
                && !(self.start_spec() == 0 && self.end_spec() == u64::MAX)
                ==> result as int == range_cardinality(self.start_spec(), self.end_spec())
                    && result >= 1
        ]
        { range_len(self.start, self.end) }
    }

    verified_const_method! {
        /// Returns true if the range is empty.
        pub fn is_empty(&self) -> [result: bool]
        ensures [result == (self.start_spec() > self.end_spec())]
        { range_is_empty(self.start, self.end) }
    }

    verified_method! {
        /// Returns whether or not the segment range includes the number.
        pub fn contains(&self, number: u64) -> [result: bool]
        ensures [
            result == (self.start_spec() <= self.end_spec()
                && self.start_spec() <= number && number <= self.end_spec())
        ]
        { range_contains(self.start, self.end, number) }
    }
}

#[cfg(not(verus_keep_ghost))]
impl core::fmt::Display for SegmentRangeInclusive {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}..={}", self.start, self.end)
    }
}

verified_from_std_range! {value, {
    // An exhausted standard inclusive range can expose its final bound as `Excluded`; the
    // referenced value is still the stored endpoint, so both bound variants convert identically.
    let start = match value.start_bound() {
        Bound::Included(start) | Bound::Excluded(start) => *start,
        Bound::Unbounded => 0,
    };
    let end = match value.end_bound() {
        Bound::Included(end) | Bound::Excluded(end) => *end,
        Bound::Unbounded => 0,
    };
    SegmentRangeInclusive { start, end }
}}

verified_to_std_range! {&SegmentRangeInclusive, value, {
    RangeInclusive::new(value.start, value.end)
}}

verified_to_std_range! {SegmentRangeInclusive, value, {
    RangeInclusive::new(value.start, value.end)
}}

#[cfg(verus_keep_ghost)]
verus! {
impl FromSpecImpl<RangeInclusive<u64>> for SegmentRangeInclusive {
    open spec fn obeys_from_spec() -> bool {
        // vstd's generic trait model does not represent exhausted inclusive-range bounds. The
        // concrete impl contract above and O8 therefore prove only the required unexhausted case.
        false
    }

    open spec fn from_spec(value: RangeInclusive<u64>) -> SegmentRangeInclusive {
        SegmentRangeInclusive { start: value@.start, end: value@.end }
    }
}

impl<'a> FromSpecImpl<&'a SegmentRangeInclusive> for RangeInclusive<u64> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: &'a SegmentRangeInclusive) -> RangeInclusive<u64> {
        spec_range_inclusive_new(value.start, value.end)
    }
}

impl FromSpecImpl<SegmentRangeInclusive> for RangeInclusive<u64> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: SegmentRangeInclusive) -> RangeInclusive<u64> {
        spec_range_inclusive_new(value.start, value.end)
    }
}

fn empty_range_laws(start: u64, end: u64, number: u64) -> (result: (u64, bool))
    requires start > end,
    ensures result.0 == 0, !result.1,
{
    (range_len(start, end), range_contains(start, end, number))
}

fn nonempty_range_length_laws(start: u64, end: u64) -> (result: u64)
    requires
        start <= end,
        !(start == 0 && end == u64::MAX),
    ensures
        result as int == range_cardinality(start, end),
        result >= 1,
{
    range_len(start, end)
}

fn full_domain_laws(number: u64) -> (result: (u64, bool))
    ensures result.0 == u64::MAX, result.1,
{
    (range_len(0, u64::MAX), range_contains(0, u64::MAX, number))
}

fn member_offset_is_safe(start: u64, end: u64, number: u64) -> (result: u64)
    requires start <= end, start <= number, number <= end,
    ensures
        result as int == number as int - start as int,
        (result as int) < range_cardinality(start, end),
{
    let is_member = range_contains(start, end, number);
    assert(is_member);
    number - start
}

fn singleton_laws(value: u64, number: u64) -> (result: (u64, bool, bool))
    ensures result.0 == 1, !result.1, result.2 == (number == value),
{
    (
        range_len(value, value),
        range_is_empty(value, value),
        range_contains(value, value, number),
    )
}

fn endpoint_round_trip_laws(
    start: u64,
    end: u64,
    number: u64,
) -> (result: (SegmentRangeInclusive, bool, bool))
    ensures
        result.0.start_spec() == start,
        result.0.end_spec() == end,
        result.1 == (start > end),
        result.2 == (start <= end && start <= number && number <= end),
{
    let standard = RangeInclusive::new(start, end);
    let converted = SegmentRangeInclusive::from(standard);
    let is_empty = converted.is_empty();
    let custom_contains = converted.contains(number);

    let borrowed_round_trip = RangeInclusive::from(&converted);
    assert(borrowed_round_trip@.start == start && borrowed_round_trip@.end == end);
    let standard_contains = borrowed_round_trip.contains(&number);
    assert(standard_contains == custom_contains);

    let owned_round_trip = RangeInclusive::from(converted);
    assert(owned_round_trip@.start == start && owned_round_trip@.end == end);

    let custom_source = SegmentRangeInclusive::new(start, end);
    let standard_from_custom = RangeInclusive::from(custom_source);
    let custom_round_trip = SegmentRangeInclusive::from(standard_from_custom);
    assert(custom_round_trip.start_spec() == start && custom_round_trip.end_spec() == end);

    (converted, is_empty, standard_contains)
}

fn public_method_refinement(
    start: u64,
    end: u64,
    number: u64,
) -> (result: (SegmentRangeInclusive, u64, bool, bool))
    ensures
        result.0.start_spec() == start,
        result.0.end_spec() == end,
        result.2 == (start > end),
        result.3 == (start <= end && start <= number && number <= end),
        start > end ==> result.1 == 0,
        start <= end && start == 0 && end == u64::MAX ==> result.1 == u64::MAX,
        start <= end && !(start == 0 && end == u64::MAX)
            ==> result.1 as int == range_cardinality(start, end) && result.1 >= 1,
{
    let range = SegmentRangeInclusive::new(start, end);
    (range, range.len(), range.is_empty(), range.contains(number))
}
}
