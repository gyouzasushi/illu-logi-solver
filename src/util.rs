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

#[derive(Clone)]
pub struct Segments {
    exist: Vec<bool>,
}
impl Segments {
    pub fn new(exist: Vec<bool>) -> Self {
        Self { exist }
    }
    pub fn left(&self, i: usize) -> usize {
        let mut l = i;
        while l > 0 && self.exist[l - 1] {
            l -= 1;
        }
        l
    }
    pub fn right(&self, i: usize) -> usize {
        let mut r = i;
        while r < self.exist.len() && self.exist[r] {
            r += 1;
        }
        r
    }
    pub fn left_right(&self, i: usize) -> (usize, usize) {
        (self.left(i), self.right(i))
    }
    pub fn size(&self, i: usize) -> usize {
        self.right(i) - self.left(i)
    }
    pub fn insert(&mut self, i: usize) {
        self.exist[i] = true;
    }
    pub fn erase(&mut self, i: usize) {
        self.exist[i] = false;
    }
    pub fn all(&self, l: usize, r: usize) -> bool {
        self.exist.iter().take(r).skip(l).all(|&x| x)
    }
    pub fn is_empty(&self) -> bool {
        self.exist.iter().all(|&x| !x)
    }
    pub fn segments(&self) -> Vec<(usize, usize)> {
        let mut ret = Vec::new();
        let mut l = 0;
        while l < self.exist.len() {
            while l < self.exist.len() && !self.exist[l] {
                l += 1;
            }
            if l == self.exist.len() {
                break;
            }
            let r = self.right(l);
            ret.push((l, r));
            l = r;
        }
        ret
    }
}

#[derive(Clone)]
pub struct BitSet {
    exist: Vec<bool>,
}
impl BitSet {
    pub fn new(exist: Vec<bool>) -> Self {
        Self { exist }
    }
    pub fn insert(&mut self, i: usize) {
        self.exist[i] = true;
    }
    pub fn clear(&mut self) {
        self.exist = self.exist.iter().map(|_| false).collect()
    }
    pub fn min(&self) -> Option<usize> {
        self.exist.iter().position(|x| *x)
    }
    pub fn contains(&self, i: &usize) -> bool {
        self.exist[*i]
    }
    pub fn count_ge(&self, i: &usize) -> usize {
        self.exist.iter().skip(*i).filter(|&&x| x).count()
    }
    pub fn count_gt(&self, i: &usize) -> usize {
        self.count_ge(i) - self.exist[*i] as usize
    }
    pub fn count_le(&self, i: &usize) -> usize {
        self.count_lt(i) + self.exist[*i] as usize
    }
    pub fn count_lt(&self, i: &usize) -> usize {
        self.exist.iter().take(*i).filter(|&&x| x).count()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_segment() {
        let mut segment = Segments {
            exist: vec![
                true, true, true, true, false, false, false, false, true, true, true, true, false,
                false, false, false, true, true, true, true, false, false, false, false, true,
                true, true, true, false, true,
            ],
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
        assert_eq!(
            segment.exist,
            vec![
                true, true, true, true, false, false, false, false, true, true, false, true, false,
                false, false, false, true, true, true, true, false, false, false, false, true,
                true, true, true, false, true
            ]
        );
        segment.insert(10);
        assert_eq!(
            segment.exist,
            vec![
                true, true, true, true, false, false, false, false, true, true, true, true, false,
                false, false, false, true, true, true, true, false, false, false, false, true,
                true, true, true, false, true
            ]
        );

        assert!(segment.all(0, 4));
        assert!(!segment.all(0, 5));

        let mut segment = Segments {
            exist: vec![
                true, true, true, true, false, false, false, false, true, true, true, true, false,
                false, false, false, true, true, true, true, false, false, false, false, true,
                true, true, true, false, false, false, false,
            ],
        };
        assert_eq!(
            segment.segments(),
            vec![(0, 4,), (8, 12,), (16, 20,), (24, 28,),]
        );
        let mut segment = Segments {
            exist: vec![
                false, false, false, false, true, true, true, true, false, false, false, false,
                true, true, true, true, false, false, false, false, true, true, true, true, false,
                false, false, false, true, true, true, true,
            ],
        };
        assert_eq!(
            segment.segments(),
            vec![(4, 8,), (12, 16,), (20, 24,), (28, 32,),]
        );
        let mut segment = Segments {
            exist: vec![
                true, false, true, true, true, true, true, true, true, true, true, true, true,
                true, true, true, true, true, true, true, true, true, true, true, true, true, true,
                true, true, true, true, true,
            ],
        };
        assert!(segment.all(4, 8));
    }

    #[test]
    fn test_bitset() {
        let mut bitset = BitSet {
            exist: vec![false; 32],
        };
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
