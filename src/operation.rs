/// 行内の8推論規則。`Action.by` と `Hint` はこの型を持つ
/// （「ヒントは常に行内規則」が型レベルで保証される）。
///
/// # `Action.range` と `Operation` ペイロードの役割分担
///
/// `Action`（`crate::solver::Action`）は「どこを・どんな状態に塗ったか」を
/// `range`/`state` で持ち、「なぜ塗れると分かったか（根拠）」は `by: Operation`
/// が持つ、という役割分担で統一している。**`Operation` の各 variant の
/// ペイロードは、塗った範囲そのものではなく根拠の区間・IDである**
/// （両者が偶然一致する variant もあるが、意味としては別物）。例えば
/// `BlackIfLeftBounded(l, r)` の `l..r` は「非白領域の左端 `l` から、
/// 黒だと確定できる右端 `r` まで」という根拠区間であり、塗る範囲
/// （`Action.range`）はこの根拠区間の部分集合になる。
///
/// ペイロードそのものは「アンカー＋ヒント時点のスナップショットから、その
/// 推論の説明を一意に再構成できるか」を基準に絞ってある（詳細は
/// REFACTORING_PLAN.md D項）。再構成できないものだけをペイロードに昇格
/// させ（`BlackIfOverlap` の `id`、`WhiteIfTooLong` の `id`）、それ以外の
/// 6 variant はアンカー `(l, r)` だけで説明が一意に決まる。行コンテキスト
/// 全体（候補ブロックID範囲・ブロックごとの配置可能範囲）は `Operation` には
/// 持たせず、`hint()` がスナップショットから事後的に算出して `Hint`
/// （`possible_ids`/`blocks`）に載せる。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    /// 最左配置と最右配置の重複部分。ブロックをどちらに寄せても `[l, r)` は必ず黒になる。
    /// `id` は根拠ブロック（同じ範囲を複数ブロックが説明し得るため、
    /// アンカーだけでは一意に再構成できずペイロードに昇格させた）。
    BlackIfOverlap {
        /// 重複区間の左端。
        l: usize,
        /// 重複区間の右端（半開区間）。
        r: usize,
        /// 根拠ブロックのID（0始まり）。
        id: usize,
    },
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
    WhiteIfTooLong {
        /// 白だと確定できるセルの位置。
        j: usize,
        /// そのセルの唯一の候補ブロックのID（0始まり）。
        id: usize,
    },
    /// `[l, r)` が最小ブロックサイズより短い。
    WhiteIfTooShort(usize, usize),
    /// どのブロックを置いても `[l, r)` を黒にできない。
    WhiteIfNoBlockCovers(usize, usize),
}
