import ZombieDamage.Exceptions
namespace ZombieDamage.Exceptions
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def k4_0 : TrapData .k4 where
  allowed v := bit 0 v.val
  pre z s := bit (#[15, 15, 15, 15][z.val]!) s.val
  post z s := bit (#[0, 0, 0, 0][z.val]!) s.val
theorem k4_0_valid : k4_0.Valid := by decide

def k33_0 : TrapData .k33 where
  allowed v := bit 54 v.val
  pre z s := bit (#[63, 62, 62, 63, 55, 55][z.val]!) s.val
  post z s := bit (#[54, 4, 2, 54, 32, 16][z.val]!) s.val
theorem k33_0_valid : k33_0.Valid := by decide

def prism3_0 : TrapData .prism3 where
  allowed v := bit 18 v.val
  pre z s := bit (#[31, 23, 55, 59, 58, 62][z.val]!) s.val
  post z s := bit (#[2, 0, 2, 16, 0, 16][z.val]!) s.val
theorem prism3_0_valid : prism3_0.Valid := by decide

def prism3_1 : TrapData .prism3 where
  allowed v := bit 36 v.val
  pre z s := bit (#[47, 55, 39, 61, 62, 60][z.val]!) s.val
  post z s := bit (#[4, 4, 0, 32, 32, 0][z.val]!) s.val
theorem prism3_1_valid : prism3_1.Valid := by decide

def cube_0 : TrapData .cube where
  allowed v := bit 170 v.val
  pre z s := bit (#[191, 43, 239, 142, 251, 178, 254, 232][z.val]!) s.val
  post z s := bit (#[42, 0, 138, 0, 162, 0, 168, 0][z.val]!) s.val
theorem cube_0_valid : cube_0.Valid := by decide

def cube_1 : TrapData .cube where
  allowed v := bit 204 v.val
  pre z s := bit (#[223, 239, 77, 142, 253, 254, 212, 232][z.val]!) s.val
  post z s := bit (#[76, 140, 0, 0, 196, 200, 0, 0][z.val]!) s.val
theorem cube_1_valid : cube_1.Valid := by decide

def cube_2 : TrapData .cube where
  allowed v := bit 240 v.val
  pre z s := bit (#[247, 251, 253, 254, 113, 178, 212, 232][z.val]!) s.val
  post z s := bit (#[112, 176, 208, 224, 0, 0, 0, 0][z.val]!) s.val
theorem cube_2_valid : cube_2.Valid := by decide

theorem not_full_damage (g : Kind) : ¬ FullGame.FullDamage (graph g) := by
  cases g with
  | k4 =>
    apply FullGame.not_fullDamage_of_traps (graph .k4) (0 : Fin 4)
    intro v _
    have coverage : ∀ v : Fin 4, k4_0.pre 0 v = true := by decide
    have hc := coverage v
    exact ⟨k4_0.toTrap k4_0_valid, hc⟩
  | k33 =>
    apply FullGame.not_fullDamage_of_traps (graph .k33) (0 : Fin 6)
    intro v _
    have coverage : ∀ v : Fin 6, k33_0.pre 0 v = true := by decide
    have hc := coverage v
    exact ⟨k33_0.toTrap k33_0_valid, hc⟩
  | prism3 =>
    apply FullGame.not_fullDamage_of_traps (graph .prism3) (0 : Fin 6)
    intro v _
    have coverage : ∀ v : Fin 6, prism3_0.pre 0 v = true ∨ prism3_1.pre 0 v = true := by decide
    have hc := coverage v
    rcases hc with h0 | h1
    · exact ⟨prism3_0.toTrap prism3_0_valid, h0⟩
    · exact ⟨prism3_1.toTrap prism3_1_valid, h1⟩
  | cube =>
    apply FullGame.not_fullDamage_of_traps (graph .cube) (0 : Fin 8)
    intro v _
    have coverage : ∀ v : Fin 8, cube_0.pre 0 v = true ∨ cube_1.pre 0 v = true ∨ cube_2.pre 0 v = true := by decide
    have hc := coverage v
    rcases hc with h0 | h1 | h2
    · exact ⟨cube_0.toTrap cube_0_valid, h0⟩
    · exact ⟨cube_1.toTrap cube_1_valid, h1⟩
    · exact ⟨cube_2.toTrap cube_2_valid, h2⟩
end ZombieDamage.Exceptions
