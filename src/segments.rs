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
    pub fn size(&self, i: usize) -> usize {
        self.right(i) - self.left(i)
    }
    pub fn insert(&mut self, i: usize) {
        self.exist[i] = true;
    }
    pub fn erase(&mut self, i: usize) {
        self.exist[i] = false;
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

        assert!(segment.exist[0..4].iter().all(|&x| x));
        assert!(!segment.exist[0..5].iter().all(|&x| x));

        let segment = Segments {
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
        let segment = Segments {
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
        let segment = Segments {
            exist: vec![
                true, false, true, true, true, true, true, true, true, true, true, true, true,
                true, true, true, true, true, true, true, true, true, true, true, true, true, true,
                true, true, true, true, true,
            ],
        };
        assert!(segment.exist[4..8].iter().all(|&x| x));
    }
}
