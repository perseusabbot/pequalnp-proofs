import Disjoint

namespace Checkpoint140

open Finset PEqualNP.Outside.L_meta_9338

/-- The row masks and the column masks each have empty intersection. -/
def apart (a b : H) : Bool :=
  let x := ovals[a.val]!
  let y := ovals[b.val]!
  (x.1 &&& y.1 == 0) && (x.2 &&& y.2 == 0)

private def pairMoves : Array (List G) := #[[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[4,2,3,0],[],[],[],[],[],[],[],[],[],[0,5,8,0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[5,1,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1,0,3,2],[],[],[],[],[],[],[],[2,8,4,0],[],[],[],[],[],[],[],[],[],[],[],[6,4,6,1],[],[],[],[],[],[],[],[],[4,3,1],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1,4,8],[2,2,6],[],[],[],[],[],[5,1,0,0],[],[],[],[],[],[],[]]

private def routeOK (a b : H) : Bool :=
  let y := walk (firstMoves[a.val]!) b
  let v := pairMoves[y.val]!
  !(apart a b) || ((walk v 0 == 13) && (walk v y == 14))

private def routeRow (i : Nat) : Bool :=
  scan (fun j => routeOK (Fin.ofNat 168 i) (Fin.ofNat 168 j)) 0 168

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows0 : ValidOn routeRow 0 16 := scanned _ 0 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows16 : ValidOn routeRow 16 32 := scanned _ 16 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows32 : ValidOn routeRow 32 48 := scanned _ 32 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows48 : ValidOn routeRow 48 64 := scanned _ 48 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows64 : ValidOn routeRow 64 80 := scanned _ 64 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows80 : ValidOn routeRow 80 96 := scanned _ 80 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows96 : ValidOn routeRow 96 112 := scanned _ 96 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows112 : ValidOn routeRow 112 128 := scanned _ 112 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows128 : ValidOn routeRow 128 144 := scanned _ 128 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows144 : ValidOn routeRow 144 160 := scanned _ 144 16 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem rows160 : ValidOn routeRow 160 168 := scanned _ 160 8 (by decide +kernel)

private theorem allRows : ValidOn routeRow 0 168 := (combine (combine (combine rows0 rows16) (combine rows32 (combine rows48 rows64))) (combine (combine rows80 (combine rows96 rows112)) (combine rows128 (combine rows144 rows160))))

private theorem routes (a b : H) (d : apart a b = true) :
    let y := walk (firstMoves[a.val]!) b
    let v := pairMoves[y.val]!
    walk v 0 = 13 ∧ walk v y = 14 := by
  have h := allRows a.val (by omega) a.isLt
  simp only [routeRow,Fin.ofNat_val_eq_self] at h
  have z := scanned _ 0 168 h b.val (by omega) b.isLt
  simpa only [routeOK,Fin.ofNat_val_eq_self,d,Bool.not_true,Bool.false_or,Bool.and_eq_true,
    beq_iff_eq] using z

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem apartCount : (∑ a : H, ∑ b : H, if a < b ∧ apart a b = true then (1 : Nat) else 0) = 840 := by
  decide +kernel

private def Exceptional (T : Finset Box) := ∀ b ∈ T, ∀ h : H, ¬fits b (oval h)

private def inverseLabels : Array (Array H) := #[
#[15,137,93,98,144,146,50,164,91,161,5,18,163,53,22,11,135,89,145,56,95,86,23,143,14,0,139,162,55,51,97,4,10,134,90,142,109,20,133,138,88,141,54,110,85,12,136,17,2,52,21,8,96,140,84,3,7,127,25,32,158,103,37,47,159,128,106,41,131,122,45,107,126,24,48,35,31,120,30,44,99,34,130,40,160,157,129,28,108,49,42,132,33,39,101,125,105,123,46,156,102,29,26,38,100,36,121,43,27,124,104,92,19,16,1,87,13,6,94,9,113,166,63,152,119,83,57,69,155,82,116,67,153,114,70,62,167,68,112,65,111,115,66,154,64,71,60,165,74,79,72,117,77,149,118,147,76,73,81,148,75,150,78,151,80,58,59,61],
#[26,108,9,30,132,139,163,130,92,47,84,100,159,140,91,102,55,99,160,144,1,24,8,138,105,109,22,34,123,134,45,52,46,95,40,145,122,119,68,76,118,167,150,147,77,80,115,78,82,166,65,75,61,153,117,112,60,97,38,50,94,44,156,161,32,20,126,121,14,33,137,120,56,101,142,2,10,81,113,155,58,57,116,148,19,35,36,110,128,124,136,98,42,162,41,96,158,18,129,107,13,7,89,143,74,66,83,154,62,71,149,103,88,4,28,6,12,43,79,67,106,16,104,21,127,133,39,51,146,157,37,54,15,31,3,27,131,86,87,11,59,72,64,151,114,111,73,48,85,141,0,25,135,17,165,69,5,29,164,49,93,23,125,70,152,53,90,63],
#[84,50,118,77,52,109,2,117,47,32,115,68,34,116,140,163,161,147,134,142,130,159,167,153,0,85,51,72,3,86,48,69,141,133,165,135,131,38,100,26,58,101,105,61,94,81,76,156,121,123,104,39,59,27,16,157,151,110,88,4,74,79,89,7,35,83,107,71,162,136,143,149,53,5,90,70,164,28,42,43,19,124,29,125,24,99,82,57,40,112,60,55,14,95,120,166,122,138,145,25,37,111,15,17,1,78,33,148,160,73,87,41,62,96,18,158,154,63,6,49,44,30,113,119,45,65,20,97,56,22,126,155,139,106,114,64,31,21,127,146,92,9,80,75,108,150,132,103,66,67,98,128,23,152,13,36,8,91,10,137,144,54,11,102,46,12,93,129],
#[37,75,50,25,30,54,61,44,74,13,79,63,66,43,72,82,46,57,64,27,5,41,53,12,59,78,31,10,3,40,29,6,26,65,38,9,7,73,45,11,58,80,52,2,42,28,67,39,1,60,51,24,0,8,62,77,4,119,105,87,113,101,118,111,93,103,110,88,106,91,99,85,102,112,104,90,109,92,117,100,89,86,114,84,127,144,137,148,133,141,120,152,125,154,123,155,147,128,136,150,134,142,149,124,122,135,129,121,143,126,140,166,165,164,158,163,161,156,157,162,76,22,81,56,34,17,19,49,36,71,16,33,23,55,48,14,21,70,68,35,47,15,32,20,83,69,18,108,116,94,107,95,96,97,115,98,131,145,151,132,153,139,130,146,138,160,167,159],
#[10,115,101,102,95,97,60,33,166,138,148,150,153,121,112,113,20,75,68,84,134,137,156,132,62,67,96,36,7,12,162,129,89,71,28,18,136,114,17,21,73,69,85,27,135,157,151,0,11,64,90,93,29,23,152,63,125,116,2,8,76,100,57,65,139,160,161,123,14,22,91,26,98,66,4,124,88,15,111,86,133,3,70,5,55,56,108,80,109,38,46,167,140,155,52,81,82,145,163,83,110,43,154,143,54,104,146,39,141,49,53,119,78,142,144,50,105,42,51,164,117,34,58,94,99,9,122,126,159,147,24,92,130,103,6,13,35,149,74,158,25,31,87,16,165,59,127,32,61,1,120,30,128,19,72,131,40,44,77,47,118,107,41,48,106,45,79,37],
#[51,57,119,114,72,77,25,106,111,85,54,8,99,44,73,78,38,102,1,58,100,104,80,9,15,55,69,97,32,48,115,21,76,33,108,16,94,62,53,4,93,41,79,103,110,66,12,42,29,6,83,70,98,35,96,49,36,82,50,0,91,113,37,24,84,64,118,30,39,26,59,92,68,14,47,20,81,5,63,74,88,28,18,19,86,109,65,10,117,45,31,60,2,40,101,46,87,27,61,95,116,56,17,34,90,67,7,13,43,23,107,112,11,52,3,105,75,22,89,71,166,161,144,155,165,126,133,140,147,120,157,150,121,167,146,139,159,138,160,151,164,162,152,128,154,129,124,163,137,127,141,156,130,132,158,136,135,142,122,123,148,153,131,143,149,134,145,125],
#[103,38,113,74,44,110,9,118,58,77,92,28,80,84,13,101,109,75,43,7,67,117,89,52,6,102,41,82,12,99,62,24,10,46,112,40,60,29,106,53,59,104,85,64,114,0,39,90,31,27,93,25,63,54,73,87,11,108,97,35,81,68,94,36,83,47,115,20,107,56,34,71,55,33,96,18,95,48,16,21,69,23,49,17,79,119,50,26,66,88,30,42,4,100,65,105,61,45,2,78,57,91,1,8,72,5,51,3,86,37,111,76,19,98,32,116,22,14,70,15,150,155,156,163,147,136,126,162,140,121,149,134,143,166,158,137,154,129,148,122,165,152,127,141,157,125,135,167,132,130,159,153,138,145,151,146,128,161,124,142,123,144,120,164,133,139,160,131],
#[110,10,140,162,55,96,56,138,134,137,52,89,145,20,109,7,12,143,95,97,163,136,84,18,101,43,102,129,108,36,156,28,38,46,121,33,132,90,54,93,135,17,21,146,141,0,11,85,53,23,104,29,157,49,125,27,39,40,44,103,122,126,34,107,158,24,130,47,99,41,35,159,6,13,94,92,9,25,31,48,127,106,87,16,166,154,62,67,167,115,83,112,113,71,155,60,153,82,68,148,150,80,75,81,152,114,63,69,64,73,151,149,117,118,74,147,77,58,165,59,142,144,2,8,139,98,50,88,14,22,161,4,91,124,100,42,160,105,123,26,133,164,51,15,3,86,5,120,45,32,30,128,19,1,131,37,119,66,116,57,65,78,76,111,70,79,61,72],
#[7,106,143,140,41,40,93,122,163,127,89,84,158,11,110,109,31,162,99,54,136,134,52,24,85,90,44,126,12,10,141,0,53,103,135,25,137,104,13,9,157,87,46,129,125,39,92,27,29,102,43,38,121,6,156,101,28,107,23,21,159,146,95,96,130,47,145,18,34,35,55,138,48,97,17,20,56,16,108,49,132,36,94,33,147,149,77,114,154,60,62,118,64,112,152,117,166,74,82,165,155,67,113,63,150,80,59,73,75,58,148,167,115,71,68,153,83,69,151,81,164,128,86,45,144,8,5,3,37,91,133,51,30,142,2,4,120,88,161,50,123,124,42,1,105,100,26,131,98,15,22,139,14,32,160,19,66,65,111,72,119,79,57,61,78,70,116,76]
]
private def inverseAt (g : G) (i : Nat) : Bool :=
  let h : H := Fin.ofNat 168 i
  act g ((inverseLabels[g.val]!)[h.val]!) == h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse0 : ValidOn (inverseAt 0) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse1 : ValidOn (inverseAt 1) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse2 : ValidOn (inverseAt 2) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse3 : ValidOn (inverseAt 3) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse4 : ValidOn (inverseAt 4) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse5 : ValidOn (inverseAt 5) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse6 : ValidOn (inverseAt 6) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse7 : ValidOn (inverseAt 7) 0 168 := scanned _ 0 168 (by decide +kernel)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem inverse8 : ValidOn (inverseAt 8) 0 168 := scanned _ 0 168 (by decide +kernel)

private theorem inverseCert (g : G) (h : H) : act g ((inverseLabels[g.val]!)[h.val]!) = h := by
  have allI : ValidOn (inverseAt g) 0 168 := by
    fin_cases g
    · exact inverse0
    · exact inverse1
    · exact inverse2
    · exact inverse3
    · exact inverse4
    · exact inverse5
    · exact inverse6
    · exact inverse7
    · exact inverse8
  have v := allI h.val (by omega) h.isLt
  simpa only [inverseAt,Fin.ofNat_val_eq_self,beq_iff_eq] using v

private theorem surjAct (g : G) (h : H) : ∃ j : H, act g j = h := ⟨_,inverseCert g h⟩

private theorem movedExceptional (g : G) {T : Finset Box} (e : Exceptional T) :
    Exceptional (T.image (moved g)) := by
  rintro _ hm h fitsH
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hm
  obtain ⟨j,rfl⟩ := surjAct g h
  rw [←genOval] at fitsH
  have hr : Function.Injective (permR g) := Finite.injective_iff_surjective.mpr (genFacts g).2.1
  have hc : Function.Injective (permC g) := Finite.injective_iff_surjective.mpr (genFacts g).2.2
  exact e b hb j ⟨fun p hp => hr.mem_finset_image.mp (fitsH.1 (mem_image_of_mem _ hp)),
    fun q hq => hc.mem_finset_image.mp (fitsH.2 (mem_image_of_mem _ hq))⟩

private theorem walkPair (w : List G) (a b : H) (T : Finset Box) (ok : family T)
    (e : Exceptional T) (c : covered [a,b] T) :
    ∃ U : Finset Box, U.card ≤ T.card ∧ family U ∧ Exceptional U ∧ covered [walk w a,walk w b] U := by
  induction w generalizing a b T with
  | nil => exact ⟨T,le_rfl,ok,e,c⟩
  | cons g t ih =>
    obtain ⟨U,ct,f,e',cv⟩ := ih (act g a) (act g b) (T.image (moved g))
      (movedFamily g ok) (movedExceptional g e) (movedCover g c)
    exact ⟨U,ct.trans card_image_le,f,e',cv⟩

/-- Every disjoint pair of maximum rectangles excludes eleven exceptional companions. -/
theorem disjointPairsImpossible (a b : H) (separate : apart a b = true) (T : Finset Box)
    (budget : T.card ≤ 11) (ok : family T) (exceptional : ∀ c ∈ T, ∀ h : H, ¬fits c (oval h)) :
    ¬covered [a,b] T := by
  intro cover
  let u := firstMoves[a.val]!
  let y := walk u b
  let v := pairMoves[y.val]!
  obtain ⟨U,cu,fu,eu,coverU⟩ := walkPair u a b T ok exceptional cover
  have first : walk u a = 0 := startFacts.1 a
  rw [first] at coverU
  obtain ⟨Z,cz,fz,ez,coverZ⟩ := walkPair v 0 y U fu eu coverU
  have r := routes a b separate
  change walk v 0 = 13 ∧ walk v y = 14 at r
  rw [r.1,r.2] at coverZ
  exact disjointPairImpossible Z (cz.trans (cu.trans budget)) fz ez coverZ

#print axioms apartCount
#print axioms disjointPairsImpossible

end Checkpoint140
