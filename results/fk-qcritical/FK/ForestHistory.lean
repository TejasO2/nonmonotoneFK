import FK.SegmentAttachment
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Finite straight-segment attachment histories

A history starts with a finite point set and attaches a segment meeting the
old carrier exactly at one endpoint.  Such histories have compact carriers
and path-connected complements.  An actual `FiniteArcEmbedding` whose carrier
is one of these history carriers consequently has exactly one face.
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval
open FK.PlaneTopology.Continuous.Segment

/-- Finite straight-arc forest growth by isolated initial components and
one-endpoint segment attachments. -/
inductive StraightAttachmentHistory : Set Plane → Type
  | finitePoints (s : Finset Plane) : StraightAttachmentHistory ↑s
  | attach {K : Set Plane} (H : StraightAttachmentHistory K) (a b : Plane)
      (hab : a ≠ b) (hinter : K ∩ [a -[ℝ] b] = {a}) :
      StraightAttachmentHistory (K ∪ [a -[ℝ] b])

namespace StraightAttachmentHistory

/-- Every history carrier is compact. -/
theorem isCompact_carrier {K : Set Plane} (H : StraightAttachmentHistory K) :
    IsCompact K := by
  induction H with
  | finitePoints s => exact s.finite_toSet.isCompact
  | attach H a b hab hinter ih =>
      exact ih.union (isCompact_straightSegment a b)

/-- Every history carrier has path-connected complement. -/
theorem isPathConnected_compl_carrier {K : Set Plane}
    (H : StraightAttachmentHistory K) : IsPathConnected Kᶜ := by
  induction H with
  | finitePoints s =>
      have hrank : 1 < Module.rank ℝ Plane := by
        simp
        norm_num
      exact s.finite_toSet.countable.isPathConnected_compl_of_one_lt_rank hrank
  | attach H a b hab hinter ih =>
      exact isPathConnected_compl_union_segment_of_attached
        (isCompact_carrier H) hab hinter ih

end StraightAttachmentHistory

open StraightAttachmentHistory

/-- An actual continuous finite-arc embedding with a straight attachment
history carrier has exactly one complementary face. -/
theorem face_subsingleton_of_attachmentHistory
    {L : FK.Finite.LabelledMultigraph} {K : Set Plane}
    (H : StraightAttachmentHistory K) (E : FiniteArcEmbedding L)
    (hcarrier : E.carrier = K) : Subsingleton E.Face := by
  have hp : IsPathConnected E.carrierᶜ := by
    rw [hcarrier]
    exact H.isPathConnected_compl_carrier
  letI : PathConnectedSpace E.FacePoints := isPathConnected_iff_pathConnectedSpace.mp hp
  infer_instance

/-- The unique actual face of an attachment-history embedding is nonempty. -/
theorem face_nonempty_of_attachmentHistory
    {L : FK.Finite.LabelledMultigraph} {K : Set Plane}
    (H : StraightAttachmentHistory K) (E : FiniteArcEmbedding L)
    (hcarrier : E.carrier = K) : Nonempty E.Face := by
  have hp : IsPathConnected E.carrierᶜ := by
    rw [hcarrier]
    exact H.isPathConnected_compl_carrier
  letI : PathConnectedSpace E.FacePoints := isPathConnected_iff_pathConnectedSpace.mp hp
  infer_instance

end
end FK.PlaneTopology.Continuous.Forest
