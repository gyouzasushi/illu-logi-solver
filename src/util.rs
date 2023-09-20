pub trait SetMinMax {
    fn setmin(&mut self, v: Self) -> bool;
    fn setmax(&mut self, v: Self) -> bool;
}
impl<T> SetMinMax for T
where
    T: PartialOrd,
{
    fn setmin(&mut self, v: T) -> bool {
        *self > v && {
            *self = v;
            true
        }
    }
    fn setmax(&mut self, v: T) -> bool {
        *self < v && {
            *self = v;
            true
        }
    }
}

const SIZE: usize = 32;
#[derive(Clone)]
pub struct Segments {
    _bit: u32,
}
impl Segments {
    pub fn new() -> Self {
        Self { _bit: 0 }
    }
    pub fn initialize(self, n: usize) -> Self {
        Self { _bit: (1 << n) - 1 }
    }
    pub fn left(&self, i: usize) -> usize {
        SIZE - (self._bit | (!((1 << (i + 1)) - 1))).leading_ones() as usize
    }
    pub fn right(&self, i: usize) -> usize {
        (self._bit >> i).trailing_ones() as usize + i
    }
    pub fn left_right(&self, i: usize) -> (usize, usize) {
        (self.left(i), self.right(i))
    }
    pub fn size(&self, i: usize) -> usize {
        self.right(i) - self.left(i)
    }
    pub fn insert(&mut self, i: usize) {
        self._bit |= 1 << i;
    }
    pub fn erase(&mut self, i: usize) {
        self._bit &= u32::MAX ^ 1 << i;
    }
    pub fn all(&self, l: usize, r: usize) -> bool {
        ((self._bit & ((1 << r) - 1)) >> l).count_ones() as usize == r - l
    }
    pub fn segments(&self) -> Vec<(usize, usize)> {
        let mut ret = Vec::new();
        let mut l = 0;
        while l < SIZE {
            l = l + (self._bit >> l).trailing_zeros() as usize;
            if l >= SIZE {
                break;
            }
            let r = l + (self._bit >> l).trailing_ones() as usize;
            ret.push((l, r));
            l = r;
        }
        ret
    }
}

#[derive(Clone)]
pub struct BitSet {
    _bit: u32,
}
impl BitSet {
    pub fn new() -> Self {
        Self { _bit: 0 }
    }
    pub fn insert(&mut self, i: usize) {
        self._bit |= 1 << i;
    }
    pub fn clear(&mut self) {
        self._bit = 0;
    }
    pub fn min(&self) -> Option<usize> {
        if self._bit == 0 {
            None
        } else {
            Some(self._bit.trailing_zeros() as usize)
        }
    }
    pub fn contains(&self, i: &usize) -> bool {
        (self._bit >> i & 1) == 1
    }
    pub fn count_ge(&self, i: &usize) -> usize {
        (self._bit >> i).count_ones() as usize
    }
    pub fn count_gt(&self, i: &usize) -> usize {
        self.count_ge(i) - (self._bit >> i & 1) as usize
    }
    pub fn count_le(&self, i: &usize) -> usize {
        self.count_lt(i) + (self._bit >> i & 1) as usize
    }
    pub fn count_lt(&self, i: &usize) -> usize {
        (self._bit & ((1 << i) - 1)).count_ones() as usize
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_segment() {
        let mut segment = Segments {
            _bit: 0b101111000011110000111100001111,
        };
        assert_eq!(segment.left(10), 8);
        assert_eq!(segment.right(10), 12);
        assert_eq!(segment.left(8), 8);
        assert_eq!(segment.right(11), 12);
        assert_eq!(segment.left(0), 0);
        assert_eq!(segment.right(27), 28);
        assert_eq!(segment.left(29), 29);
        assert_eq!(segment.right(29), 30);
        segment.erase(10);
        assert_eq!(segment._bit, 0b101111000011110000101100001111);
        segment.insert(10);
        assert_eq!(segment._bit, 0b101111000011110000111100001111);

        assert!(segment.all(0, 4));
        assert!(!segment.all(0, 5));

        let segment = Segments {
            _bit: 0b00001111000011110000111100001111,
        };
        assert_eq!(
            segment.segments(),
            vec![(0, 4,), (8, 12,), (16, 20,), (24, 28,),]
        );
        let segment = Segments {
            _bit: 0b11110000111100001111000011110000,
        };
        assert_eq!(
            segment.segments(),
            vec![(4, 8,), (12, 16,), (20, 24,), (28, 32,),]
        );
        let segment = Segments {
            _bit: 0b11111111111111111111111111111101,
        };
        assert!(segment.all(4, 8));
    }

    #[test]
    fn test_bitset() {
        let mut bitset = BitSet::new();
        assert_eq!(bitset.min(), None);
        bitset.insert(10);
        assert_eq!(bitset.min(), Some(10));
        bitset.insert(15);
        assert_eq!(bitset.min(), Some(10));
        bitset.insert(5);
        assert_eq!(bitset.min(), Some(5));
        bitset.insert(0);
        assert_eq!(bitset.min(), Some(0));

        assert_eq!(bitset.count_ge(&10), 2);
        assert_eq!(bitset.count_gt(&10), 1);
        assert_eq!(bitset.count_ge(&9), 2);
        assert_eq!(bitset.count_gt(&9), 2);

        assert_eq!(bitset.count_le(&10), 3);
        assert_eq!(bitset.count_lt(&10), 2);
        assert_eq!(bitset.count_le(&8), 2);
        assert_eq!(bitset.count_lt(&8), 2);
    }
}
