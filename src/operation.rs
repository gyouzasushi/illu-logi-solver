#[derive(Clone, Copy, Debug)]
pub enum Operation {
    /// 最左配置と最右配置の重複部分。ブロックをどちらに寄せても `[l, r)` は必ず黒になる。
    BlackIfOverlap(usize, usize),
    /// `[l, r)` は両端が確定しており、候補ブロックが全て収まりきらない。
    BlackIfBounded(usize, usize),
    /// 左端 `l` が確定しているため、最小ブロックサイズ分だけ右へ黒が続く。
    BlackIfLeftBounded(usize, usize),
    /// 右端 `r` が確定しているため、最小ブロックサイズ分だけ左へ黒が続く。
    BlackIfRightBounded(usize, usize),
    /// 黒セグメント `[l, r)` のサイズが候補ブロックの最大サイズと一致し、これ以上延びない。
    WhiteIfSegmentComplete(usize, usize),
    /// セル `j` を黒にすると唯一の候補ブロックのサイズを超えてしまう。
    WhiteIfTooLong(usize),
    /// `[l, r)` が最小ブロックサイズより短い。
    WhiteIfTooShort(usize, usize),
    /// どのブロックを置いても `[l, r)` を黒にできない。
    WhiteIfNoBlockCovers(usize, usize),
    /// 直交する行/列での確定が伝播した。
    SameStateAsOrthogonal,
}
