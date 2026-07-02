/// 行内の8推論規則。`Action.by` と `Hint` はこの型を持つ
/// （「ヒントは常に行内規則」が型レベルで保証される）。
///
/// ペイロードは「アンカー＋ヒント時点のスナップショットから、その推論の
/// 説明を一意に再構成できるか」を基準に絞ってある（詳細は
/// REFACTORING_PLAN.md D項）。塗った範囲そのものは `Action.range` が持つので、
/// ここに入るのは根拠の区間・IDのみ。
#[derive(Clone, Copy, Debug)]
pub enum Operation {
    /// 最左配置と最右配置の重複部分。ブロックをどちらに寄せても `[l, r)` は必ず黒になる。
    /// `id` は根拠ブロック（同じ範囲を複数ブロックが説明し得るため、
    /// アンカーだけでは一意に再構成できずペイロードに昇格させた）。
    BlackIfOverlap { l: usize, r: usize, id: usize },
    /// `[l, r)` は両端が確定しており、候補ブロックが全て収まりきらない。
    BlackIfBounded(usize, usize),
    /// 左端 `l` が確定しているため、最小ブロックサイズ分だけ右へ黒が続く。
    BlackIfLeftBounded(usize, usize),
    /// 右端 `r` が確定しているため、最小ブロックサイズ分だけ左へ黒が続く。
    BlackIfRightBounded(usize, usize),
    /// 黒セグメント `[l, r)` のサイズが候補ブロックの最大サイズと一致し、これ以上延びない。
    WhiteIfSegmentComplete(usize, usize),
    /// セル `j` を黒にすると唯一の候補ブロックのサイズを超えてしまう。
    /// `id` はその唯一の候補ブロック（計算済みで追加コストなし）。
    WhiteIfTooLong { j: usize, id: usize },
    /// `[l, r)` が最小ブロックサイズより短い。
    WhiteIfTooShort(usize, usize),
    /// どのブロックを置いても `[l, r)` を黒にできない。
    WhiteIfNoBlockCovers(usize, usize),
}
