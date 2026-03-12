import re

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # GaussianHelpers.lean
    if 'GaussianHelpers.lean' in filepath:
        content = content.replace('ring!', 'ring_nf!')
        content = content.replace('\n    ring\n', '\n    ring_nf\n')
        content = content.replace('\n      ring\n', '\n      ring_nf\n')
        content = content.replace('\n  ring\n', '\n  ring_nf\n')
        content = content.replace('(hρ : 0 < ρ_ion)', '(_hρ : 0 < ρ_ion)')
        content = content.replace('(hf_int : Integrable', '(_hf_int : Integrable')
        content = content.replace('(hf_pos : ∀ v', '(_hf_pos : ∀ v')
        content = content.replace('simp_all [ div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm ]', 'simp_all [ div_eq_mul_inv, mul_comm, mul_left_comm ]')
        content = content.replace('simp_all [ add_mul, div_eq_mul_inv, MeasureTheory.integral_const_mul ]', 'simp_all [ add_mul, div_eq_mul_inv ]')
        content = content.replace('simp [ mul_assoc, ← Real.exp_sum, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, normSq ]', 'simp [ ← Real.exp_sum, Finset.sum_add_distrib, normSq ]')
        content = content.replace('simp_all [ Finset.prod_erase_mul _ _ (Finset.mem_univ i) ]', 'simp_all')
        content = content.replace('simp [ Real.exp_add, mul_add, add_comm,\n         add_left_comm, mul_assoc, mul_comm, mul_left_comm,\n         MeasureTheory.integral_const_mul,\n         MeasureTheory.integral_mul_const ]', 'simp [ Real.exp_add, mul_add, add_comm,\n         mul_assoc, mul_comm, mul_left_comm,\n         MeasureTheory.integral_const_mul ]')
        content = content.replace('simp_all [ Real.exp_add,\n           MeasureTheory.integral_const_mul,\n           MeasureTheory.integral_mul_const ]', 'simp_all [ Real.exp_add,\n           MeasureTheory.integral_const_mul ]')
        content = content.replace('simp_all [ mul_assoc, mul_comm, mul_left_comm ]', 'simp_all [ mul_comm, mul_left_comm ]')
        content = content.replace('show', 'change')

    # Section3Helpers.lean
    if 'Section3Helpers.lean' in filepath:
        content = content.replace('\n    ring\n', '\n    ring_nf\n')
        content = content.replace('\n      ring\n', '\n      ring_nf\n')
        content = content.replace('\n  ring\n', '\n  ring_nf\n')
        content = content.replace('ring!', 'ring_nf!')
        content = content.replace('simp [Pi.single_apply]', 'simp')
        content = content.replace('simp [hg_smooth.contDiffAt.differentiableAt]', 'simp')
        content = content.replace('simp [fderiv_const]', 'simp')
        content = content.replace('simp only [map_sum, map_smul, smul_eq_mul]', 'simp only [map_sum, smul_eq_mul]')
        content = content.replace('simp only [hflux, MeasureTheory.integral_zero, Pi.zero_apply]', 'simp only [hflux, MeasureTheory.integral_zero]')
        content = content.replace('simp [vDiv, fderiv_const]', 'simp [vDiv]')
        
    with open(filepath, 'w') as f:
        f.write(content)

fix_file('Aristotle/Landau/main/GaussianHelpers.lean')
fix_file('Aristotle/Landau/main/Section3Helpers.lean')
