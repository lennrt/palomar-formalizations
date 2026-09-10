import ZombieMain.AttachmentCertificate

/-! Generated explicit permutations for the 13 finite attachment rows.
Every entry and all finite-row coverage are checked by ordinary `decide`.
The unbounded family tails are separate universal proofs. -/
namespace ZombieMain.FiniteAttachments
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def aEntries : List AEntry := [
  ⟨(.ladder 2), 0, 1, 2, some ((.singleCap 2), ⟨[0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 0, 1, 3, some ((.ladder 3), ⟨[2, 3, 0, 1, 4, 5], [2, 3, 0, 1, 4, 5]⟩)⟩,
  ⟨(.ladder 2), 0, 2, 2, some ((.singleCap 2), ⟨[0, 2, 1, 3, 4], [0, 2, 1, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 0, 2, 3, some ((.ladder 3), ⟨[2, 0, 3, 1, 4, 5], [1, 3, 0, 2, 4, 5]⟩)⟩,
  ⟨(.ladder 2), 0, 3, 1, some ((.doubleCap 1), ⟨[0, 2, 3, 1], [0, 3, 1, 2]⟩)⟩,
  ⟨(.ladder 2), 0, 3, 2, some ((.k23), ⟨[0, 2, 3, 1, 4], [0, 3, 1, 2, 4]⟩)⟩,
  ⟨(.ladder 2), 1, 0, 2, some ((.singleCap 2), ⟨[0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 1, 0, 3, some ((.ladder 3), ⟨[2, 3, 0, 1, 5, 4], [2, 3, 0, 1, 5, 4]⟩)⟩,
  ⟨(.ladder 2), 1, 2, 1, some ((.doubleCap 1), ⟨[2, 0, 1, 3], [1, 2, 0, 3]⟩)⟩,
  ⟨(.ladder 2), 1, 2, 2, some ((.k23), ⟨[2, 0, 1, 3, 4], [1, 2, 0, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 1, 3, 2, some ((.singleCap 2), ⟨[2, 0, 3, 1, 4], [1, 3, 0, 2, 4]⟩)⟩,
  ⟨(.ladder 2), 1, 3, 3, some ((.ladder 3), ⟨[0, 2, 1, 3, 4, 5], [0, 2, 1, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 2), 2, 0, 2, some ((.singleCap 2), ⟨[0, 2, 1, 3, 4], [0, 2, 1, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 2, 0, 3, some ((.ladder 3), ⟨[2, 0, 3, 1, 5, 4], [1, 3, 0, 2, 5, 4]⟩)⟩,
  ⟨(.ladder 2), 2, 1, 1, some ((.doubleCap 1), ⟨[2, 0, 1, 3], [1, 2, 0, 3]⟩)⟩,
  ⟨(.ladder 2), 2, 1, 2, some ((.k23), ⟨[2, 0, 1, 3, 4], [1, 2, 0, 3, 4]⟩)⟩,
  ⟨(.ladder 2), 2, 3, 2, some ((.singleCap 2), ⟨[2, 3, 0, 1, 4], [2, 3, 0, 1, 4]⟩)⟩,
  ⟨(.ladder 2), 2, 3, 3, some ((.ladder 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 2), 3, 0, 1, some ((.doubleCap 1), ⟨[0, 2, 3, 1], [0, 3, 1, 2]⟩)⟩,
  ⟨(.ladder 2), 3, 0, 2, some ((.k23), ⟨[0, 2, 3, 1, 4], [0, 3, 1, 2, 4]⟩)⟩,
  ⟨(.ladder 2), 3, 1, 2, some ((.singleCap 2), ⟨[2, 0, 3, 1, 4], [1, 3, 0, 2, 4]⟩)⟩,
  ⟨(.ladder 2), 3, 1, 3, some ((.ladder 3), ⟨[0, 2, 1, 3, 5, 4], [0, 2, 1, 3, 5, 4]⟩)⟩,
  ⟨(.ladder 2), 3, 2, 2, some ((.singleCap 2), ⟨[2, 3, 0, 1, 4], [2, 3, 0, 1, 4]⟩)⟩,
  ⟨(.ladder 2), 3, 2, 3, some ((.ladder 3), ⟨[0, 1, 2, 3, 5, 4], [0, 1, 2, 3, 5, 4]⟩)⟩,
  ⟨(.ladder 3), 0, 1, 2, some ((.singleCap 3), ⟨[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6]⟩)⟩,
  ⟨(.ladder 3), 0, 1, 3, some ((.ladder 4), ⟨[4, 5, 2, 3, 0, 1, 6, 7], [4, 5, 2, 3, 0, 1, 6, 7]⟩)⟩,
  ⟨(.ladder 3), 0, 4, 1, some ((.p3e), ⟨[3, 0, 5, 2, 4, 1], [1, 5, 3, 0, 4, 2]⟩)⟩,
  ⟨(.ladder 3), 0, 4, 2, some ((.q3v), ⟨[1, 3, 0, 2, 4, 6, 5], [2, 0, 3, 1, 4, 6, 5]⟩)⟩,
  ⟨(.ladder 3), 0, 5, 1, some ((.k33e), ⟨[4, 0, 1, 5, 3, 2], [1, 2, 5, 4, 0, 3]⟩)⟩,
  ⟨(.ladder 3), 1, 0, 2, some ((.singleCap 3), ⟨[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6]⟩)⟩,
  ⟨(.ladder 3), 1, 0, 3, some ((.ladder 4), ⟨[4, 5, 2, 3, 0, 1, 7, 6], [4, 5, 2, 3, 0, 1, 7, 6]⟩)⟩,
  ⟨(.ladder 3), 1, 4, 1, some ((.k33e), ⟨[0, 4, 5, 1, 2, 3], [0, 3, 4, 5, 1, 2]⟩)⟩,
  ⟨(.ladder 3), 1, 5, 1, some ((.p3e), ⟨[0, 3, 2, 5, 1, 4], [0, 4, 2, 1, 5, 3]⟩)⟩,
  ⟨(.ladder 3), 1, 5, 2, some ((.q3v), ⟨[3, 1, 2, 0, 6, 4, 5], [3, 1, 2, 0, 5, 6, 4]⟩)⟩,
  ⟨(.ladder 3), 4, 0, 1, some ((.p3e), ⟨[3, 0, 5, 2, 4, 1], [1, 5, 3, 0, 4, 2]⟩)⟩,
  ⟨(.ladder 3), 4, 0, 2, some ((.q3v), ⟨[1, 3, 0, 2, 4, 6, 5], [2, 0, 3, 1, 4, 6, 5]⟩)⟩,
  ⟨(.ladder 3), 4, 1, 1, some ((.k33e), ⟨[0, 4, 5, 1, 2, 3], [0, 3, 4, 5, 1, 2]⟩)⟩,
  ⟨(.ladder 3), 4, 5, 2, some ((.singleCap 3), ⟨[4, 5, 2, 3, 0, 1, 6], [4, 5, 2, 3, 0, 1, 6]⟩)⟩,
  ⟨(.ladder 3), 4, 5, 3, some ((.ladder 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 3), 5, 0, 1, some ((.k33e), ⟨[4, 0, 1, 5, 3, 2], [1, 2, 5, 4, 0, 3]⟩)⟩,
  ⟨(.ladder 3), 5, 1, 1, some ((.p3e), ⟨[0, 3, 2, 5, 1, 4], [0, 4, 2, 1, 5, 3]⟩)⟩,
  ⟨(.ladder 3), 5, 1, 2, some ((.q3v), ⟨[3, 1, 2, 0, 6, 4, 5], [3, 1, 2, 0, 5, 6, 4]⟩)⟩,
  ⟨(.ladder 3), 5, 4, 2, some ((.singleCap 3), ⟨[4, 5, 2, 3, 0, 1, 6], [4, 5, 2, 3, 0, 1, 6]⟩)⟩,
  ⟨(.ladder 3), 5, 4, 3, some ((.ladder 4), ⟨[0, 1, 2, 3, 4, 5, 7, 6], [0, 1, 2, 3, 4, 5, 7, 6]⟩)⟩,
  ⟨(.ladder 4), 0, 1, 2, some ((.singleCap 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩)⟩,
  ⟨(.ladder 4), 0, 1, 3, some ((.ladder 5), ⟨[6, 7, 4, 5, 2, 3, 0, 1, 8, 9], [6, 7, 4, 5, 2, 3, 0, 1, 8, 9]⟩)⟩,
  ⟨(.ladder 4), 0, 6, 1, some ((.q3e), ⟨[2, 0, 6, 4, 7, 5, 3, 1], [1, 7, 0, 6, 3, 5, 2, 4]⟩)⟩,
  ⟨(.ladder 4), 1, 0, 2, some ((.singleCap 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩)⟩,
  ⟨(.ladder 4), 1, 0, 3, some ((.ladder 5), ⟨[6, 7, 4, 5, 2, 3, 0, 1, 9, 8], [6, 7, 4, 5, 2, 3, 0, 1, 9, 8]⟩)⟩,
  ⟨(.ladder 4), 1, 7, 1, some ((.q3e), ⟨[0, 2, 4, 6, 5, 7, 1, 3], [0, 6, 1, 7, 2, 4, 3, 5]⟩)⟩,
  ⟨(.ladder 4), 6, 0, 1, some ((.q3e), ⟨[2, 0, 6, 4, 7, 5, 3, 1], [1, 7, 0, 6, 3, 5, 2, 4]⟩)⟩,
  ⟨(.ladder 4), 6, 7, 2, some ((.singleCap 4), ⟨[6, 7, 4, 5, 2, 3, 0, 1, 8], [6, 7, 4, 5, 2, 3, 0, 1, 8]⟩)⟩,
  ⟨(.ladder 4), 6, 7, 3, some ((.ladder 5), ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩)⟩,
  ⟨(.ladder 4), 7, 1, 1, some ((.q3e), ⟨[0, 2, 4, 6, 5, 7, 1, 3], [0, 6, 1, 7, 2, 4, 3, 5]⟩)⟩,
  ⟨(.ladder 4), 7, 6, 2, some ((.singleCap 4), ⟨[6, 7, 4, 5, 2, 3, 0, 1, 8], [6, 7, 4, 5, 2, 3, 0, 1, 8]⟩)⟩,
  ⟨(.ladder 4), 7, 6, 3, some ((.ladder 5), ⟨[0, 1, 2, 3, 4, 5, 6, 7, 9, 8], [0, 1, 2, 3, 4, 5, 6, 7, 9, 8]⟩)⟩,
  ⟨(.singleCap 1), 0, 1, 2, some ((.doubleCap 1), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.singleCap 1), 0, 1, 3, some ((.singleCap 2), ⟨[0, 1, 4, 2, 3], [0, 1, 3, 4, 2]⟩)⟩,
  ⟨(.singleCap 1), 0, 2, 2, some ((.doubleCap 1), ⟨[0, 2, 1, 3], [0, 2, 1, 3]⟩)⟩,
  ⟨(.singleCap 1), 0, 2, 3, some ((.singleCap 2), ⟨[0, 4, 1, 2, 3], [0, 2, 3, 4, 1]⟩)⟩,
  ⟨(.singleCap 1), 1, 0, 2, some ((.doubleCap 1), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.singleCap 1), 1, 0, 3, some ((.singleCap 2), ⟨[0, 1, 4, 3, 2], [0, 1, 4, 3, 2]⟩)⟩,
  ⟨(.singleCap 1), 1, 2, 2, some ((.doubleCap 1), ⟨[2, 0, 1, 3], [1, 2, 0, 3]⟩)⟩,
  ⟨(.singleCap 1), 1, 2, 3, some ((.singleCap 2), ⟨[4, 0, 1, 2, 3], [1, 2, 3, 4, 0]⟩)⟩,
  ⟨(.singleCap 1), 2, 0, 2, some ((.doubleCap 1), ⟨[0, 2, 1, 3], [0, 2, 1, 3]⟩)⟩,
  ⟨(.singleCap 1), 2, 0, 3, some ((.singleCap 2), ⟨[0, 4, 1, 3, 2], [0, 2, 4, 3, 1]⟩)⟩,
  ⟨(.singleCap 1), 2, 1, 2, some ((.doubleCap 1), ⟨[2, 0, 1, 3], [1, 2, 0, 3]⟩)⟩,
  ⟨(.singleCap 1), 2, 1, 3, some ((.singleCap 2), ⟨[4, 0, 1, 3, 2], [1, 2, 4, 3, 0]⟩)⟩,
  ⟨(.singleCap 2), 2, 3, 2, some ((.doubleCap 2), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.singleCap 2), 2, 3, 3, some ((.singleCap 3), ⟨[0, 1, 2, 3, 6, 4, 5], [0, 1, 2, 3, 5, 6, 4]⟩)⟩,
  ⟨(.singleCap 2), 2, 4, 1, none⟩,
  ⟨(.singleCap 2), 2, 4, 2, some ((.p3e), ⟨[5, 3, 2, 0, 4, 1], [3, 5, 2, 1, 4, 0]⟩)⟩,
  ⟨(.singleCap 2), 3, 2, 2, some ((.doubleCap 2), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.singleCap 2), 3, 2, 3, some ((.singleCap 3), ⟨[0, 1, 2, 3, 6, 5, 4], [0, 1, 2, 3, 6, 5, 4]⟩)⟩,
  ⟨(.singleCap 2), 3, 4, 1, none⟩,
  ⟨(.singleCap 2), 3, 4, 2, some ((.p3e), ⟨[3, 5, 0, 2, 4, 1], [2, 5, 3, 0, 4, 1]⟩)⟩,
  ⟨(.singleCap 2), 4, 2, 1, none⟩,
  ⟨(.singleCap 2), 4, 2, 2, some ((.p3e), ⟨[5, 3, 2, 0, 4, 1], [3, 5, 2, 1, 4, 0]⟩)⟩,
  ⟨(.singleCap 2), 4, 3, 1, none⟩,
  ⟨(.singleCap 2), 4, 3, 2, some ((.p3e), ⟨[3, 5, 0, 2, 4, 1], [2, 5, 3, 0, 4, 1]⟩)⟩,
  ⟨(.singleCap 3), 4, 5, 2, some ((.doubleCap 3), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.singleCap 3), 4, 5, 3, some ((.singleCap 4), ⟨[0, 1, 2, 3, 4, 5, 8, 6, 7], [0, 1, 2, 3, 4, 5, 7, 8, 6]⟩)⟩,
  ⟨(.singleCap 3), 4, 6, 1, none⟩,
  ⟨(.singleCap 3), 5, 4, 2, some ((.doubleCap 3), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.singleCap 3), 5, 4, 3, some ((.singleCap 4), ⟨[0, 1, 2, 3, 4, 5, 8, 7, 6], [0, 1, 2, 3, 4, 5, 8, 7, 6]⟩)⟩,
  ⟨(.singleCap 3), 5, 6, 1, none⟩,
  ⟨(.singleCap 3), 6, 4, 1, none⟩,
  ⟨(.singleCap 3), 6, 5, 1, none⟩,
  ⟨(.doubleCap 1), 2, 3, 1, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.doubleCap 1), 2, 3, 2, none⟩,
  ⟨(.doubleCap 1), 3, 2, 1, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.doubleCap 1), 3, 2, 2, none⟩,
  ⟨(.doubleCap 2), 4, 5, 1, some ((.prism 3), ⟨[0, 2, 1, 3, 4, 5], [0, 2, 1, 3, 4, 5]⟩)⟩,
  ⟨(.doubleCap 2), 5, 4, 1, some ((.prism 3), ⟨[0, 2, 1, 3, 4, 5], [0, 2, 1, 3, 4, 5]⟩)⟩,
  ⟨(.k23), 2, 3, 1, none⟩,
  ⟨(.k23), 2, 3, 2, some ((.k33e), ⟨[4, 5, 1, 2, 0, 3], [4, 2, 3, 5, 0, 1]⟩)⟩,
  ⟨(.k23), 2, 4, 1, none⟩,
  ⟨(.k23), 2, 4, 2, some ((.k33e), ⟨[4, 5, 1, 0, 2, 3], [3, 2, 4, 5, 0, 1]⟩)⟩,
  ⟨(.k23), 3, 2, 1, none⟩,
  ⟨(.k23), 3, 2, 2, some ((.k33e), ⟨[4, 5, 1, 2, 0, 3], [4, 2, 3, 5, 0, 1]⟩)⟩,
  ⟨(.k23), 3, 4, 1, none⟩,
  ⟨(.k23), 3, 4, 2, some ((.k33e), ⟨[4, 5, 0, 1, 2, 3], [2, 3, 4, 5, 0, 1]⟩)⟩,
  ⟨(.k23), 4, 2, 1, none⟩,
  ⟨(.k23), 4, 2, 2, some ((.k33e), ⟨[4, 5, 1, 0, 2, 3], [3, 2, 4, 5, 0, 1]⟩)⟩,
  ⟨(.k23), 4, 3, 1, none⟩,
  ⟨(.k23), 4, 3, 2, some ((.k33e), ⟨[4, 5, 0, 1, 2, 3], [2, 3, 4, 5, 0, 1]⟩)⟩,
  ⟨(.k33e), 0, 3, 1, some ((.mobius 3), ⟨[0, 3, 4, 1, 2, 5], [0, 3, 4, 1, 2, 5]⟩)⟩,
  ⟨(.k33e), 3, 0, 1, some ((.mobius 3), ⟨[0, 3, 4, 1, 2, 5], [0, 3, 4, 1, 2, 5]⟩)⟩,
  ⟨(.p3e), 0, 1, 1, some ((.prism 3), ⟨[0, 2, 4, 1, 3, 5], [0, 3, 1, 4, 2, 5]⟩)⟩,
  ⟨(.p3e), 0, 1, 2, none⟩,
  ⟨(.p3e), 1, 0, 1, some ((.prism 3), ⟨[0, 2, 4, 1, 3, 5], [0, 3, 1, 4, 2, 5]⟩)⟩,
  ⟨(.p3e), 1, 0, 2, none⟩,
  ⟨(.q3v), 3, 5, 1, none⟩,
  ⟨(.q3v), 3, 5, 2, some ((.q3e), ⟨[6, 7, 2, 3, 4, 5, 0, 1], [6, 7, 2, 3, 4, 5, 0, 1]⟩)⟩,
  ⟨(.q3v), 3, 6, 1, none⟩,
  ⟨(.q3v), 3, 6, 2, some ((.q3e), ⟨[6, 2, 7, 3, 4, 0, 5, 1], [5, 7, 1, 3, 4, 6, 0, 2]⟩)⟩,
  ⟨(.q3v), 5, 3, 1, none⟩,
  ⟨(.q3v), 5, 3, 2, some ((.q3e), ⟨[6, 7, 2, 3, 4, 5, 0, 1], [6, 7, 2, 3, 4, 5, 0, 1]⟩)⟩,
  ⟨(.q3v), 5, 6, 1, none⟩,
  ⟨(.q3v), 5, 6, 2, some ((.q3e), ⟨[6, 2, 4, 0, 7, 3, 5, 1], [3, 7, 1, 5, 2, 6, 0, 4]⟩)⟩,
  ⟨(.q3v), 6, 3, 1, none⟩,
  ⟨(.q3v), 6, 3, 2, some ((.q3e), ⟨[6, 2, 7, 3, 4, 0, 5, 1], [5, 7, 1, 3, 4, 6, 0, 2]⟩)⟩,
  ⟨(.q3v), 6, 5, 1, none⟩,
  ⟨(.q3v), 6, 5, 2, some ((.q3e), ⟨[6, 2, 4, 0, 7, 3, 5, 1], [3, 7, 1, 5, 2, 6, 0, 4]⟩)⟩,
  ⟨(.q3e), 0, 1, 1, some ((.prism 4), ⟨[0, 1, 2, 3, 6, 7, 4, 5], [0, 1, 2, 3, 6, 7, 4, 5]⟩)⟩,
  ⟨(.q3e), 1, 0, 1, some ((.prism 4), ⟨[0, 1, 2, 3, 6, 7, 4, 5], [0, 1, 2, 3, 6, 7, 4, 5]⟩)⟩
]

def bEntries : List BEntry := [
  ⟨(.ladder 2), 0, 1, 3, 2, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 0, 2, 3, 1, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 1, 0, 2, 3, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 1, 3, 2, 0, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 2, 0, 1, 3, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 2, 3, 1, 0, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 3, 1, 0, 2, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 2), 3, 2, 0, 1, some ((.k4), ⟨[0, 1, 2, 3], [0, 1, 2, 3]⟩)⟩,
  ⟨(.ladder 3), 0, 1, 4, 5, some ((.prism 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 0, 1, 5, 4, some ((.mobius 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 1, 0, 4, 5, some ((.mobius 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 1, 0, 5, 4, some ((.prism 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 4, 5, 0, 1, some ((.prism 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 4, 5, 1, 0, some ((.mobius 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 5, 4, 0, 1, some ((.mobius 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 3), 5, 4, 1, 0, some ((.prism 3), ⟨[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]⟩)⟩,
  ⟨(.ladder 4), 0, 1, 6, 7, some ((.prism 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 0, 1, 7, 6, some ((.mobius 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 1, 0, 6, 7, some ((.mobius 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 1, 0, 7, 6, some ((.prism 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 6, 7, 0, 1, some ((.prism 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 6, 7, 1, 0, some ((.mobius 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 7, 6, 0, 1, some ((.mobius 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩,
  ⟨(.ladder 4), 7, 6, 1, 0, some ((.prism 4), ⟨[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]⟩)⟩
]

theorem a_entries_valid : aEntries.all (fun e => decide (e.outcome.Valid e.diagram)) = true := by decide
theorem b_entries_valid : bEntries.all (fun e => decide (e.outcome.Valid e.diagram)) = true := by decide

theorem a_coverage_0 : ACoverage aEntries (.ladder 2) := by decide
theorem b_coverage_0 : BCoverage bEntries (.ladder 2) := by decide
theorem a_coverage_1 : ACoverage aEntries (.ladder 3) := by decide
theorem b_coverage_1 : BCoverage bEntries (.ladder 3) := by decide
theorem a_coverage_2 : ACoverage aEntries (.ladder 4) := by decide
theorem b_coverage_2 : BCoverage bEntries (.ladder 4) := by decide
theorem a_coverage_3 : ACoverage aEntries (.singleCap 1) := by decide
theorem b_coverage_3 : BCoverage bEntries (.singleCap 1) := by decide
theorem a_coverage_4 : ACoverage aEntries (.singleCap 2) := by decide
theorem b_coverage_4 : BCoverage bEntries (.singleCap 2) := by decide
theorem a_coverage_5 : ACoverage aEntries (.singleCap 3) := by decide
theorem b_coverage_5 : BCoverage bEntries (.singleCap 3) := by decide
theorem a_coverage_6 : ACoverage aEntries (.doubleCap 1) := by decide
theorem b_coverage_6 : BCoverage bEntries (.doubleCap 1) := by decide
theorem a_coverage_7 : ACoverage aEntries (.doubleCap 2) := by decide
theorem b_coverage_7 : BCoverage bEntries (.doubleCap 2) := by decide
theorem a_coverage_8 : ACoverage aEntries (.k23) := by decide
theorem b_coverage_8 : BCoverage bEntries (.k23) := by decide
theorem a_coverage_9 : ACoverage aEntries (.k33e) := by decide
theorem b_coverage_9 : BCoverage bEntries (.k33e) := by decide
theorem a_coverage_10 : ACoverage aEntries (.p3e) := by decide
theorem b_coverage_10 : BCoverage bEntries (.p3e) := by decide
theorem a_coverage_11 : ACoverage aEntries (.q3v) := by decide
theorem b_coverage_11 : BCoverage bEntries (.q3v) := by decide
theorem a_coverage_12 : ACoverage aEntries (.q3e) := by decide
theorem b_coverage_12 : BCoverage bEntries (.q3e) := by decide

theorem small_path {f : Family} (hf : f ∈ smallOpenFamilies) {p q r : Nat}
    (h : f.diagram.LegalPath p q r) : (f.diagram.adjoinPath p q r).Classified := by
  simp only [smallOpenFamilies, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ACoverage.sound a_entries_valid a_coverage_0 h
  · exact ACoverage.sound a_entries_valid a_coverage_1 h
  · exact ACoverage.sound a_entries_valid a_coverage_2 h
  · exact ACoverage.sound a_entries_valid a_coverage_3 h
  · exact ACoverage.sound a_entries_valid a_coverage_4 h
  · exact ACoverage.sound a_entries_valid a_coverage_5 h
  · exact ACoverage.sound a_entries_valid a_coverage_6 h
  · exact ACoverage.sound a_entries_valid a_coverage_7 h
  · exact ACoverage.sound a_entries_valid a_coverage_8 h
  · exact ACoverage.sound a_entries_valid a_coverage_9 h
  · exact ACoverage.sound a_entries_valid a_coverage_10 h
  · exact ACoverage.sound a_entries_valid a_coverage_11 h
  · exact ACoverage.sound a_entries_valid a_coverage_12 h

theorem small_matching {f : Family} (hf : f ∈ smallOpenFamilies) {a b c d : Nat}
    (h : f.diagram.LegalMatching a b c d) : (f.diagram.adjoinMatching a b c d).Classified := by
  simp only [smallOpenFamilies, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BCoverage.sound b_entries_valid b_coverage_0 h
  · exact BCoverage.sound b_entries_valid b_coverage_1 h
  · exact BCoverage.sound b_entries_valid b_coverage_2 h
  · exact BCoverage.sound b_entries_valid b_coverage_3 h
  · exact BCoverage.sound b_entries_valid b_coverage_4 h
  · exact BCoverage.sound b_entries_valid b_coverage_5 h
  · exact BCoverage.sound b_entries_valid b_coverage_6 h
  · exact BCoverage.sound b_entries_valid b_coverage_7 h
  · exact BCoverage.sound b_entries_valid b_coverage_8 h
  · exact BCoverage.sound b_entries_valid b_coverage_9 h
  · exact BCoverage.sound b_entries_valid b_coverage_10 h
  · exact BCoverage.sound b_entries_valid b_coverage_11 h
  · exact BCoverage.sound b_entries_valid b_coverage_12 h

end ZombieMain.FiniteAttachments
