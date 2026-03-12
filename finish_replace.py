import os

files_to_fix = [
    'Aristotle/Landau/main/Theorem42.lean',
    'Aristotle/Landau/main/Section4.lean',
    'Aristotle/Landau/main/Section5.lean',
    'Aristotle/Landau/main/Section7.lean',
    'Aristotle/Landau/main/Section8.lean',
    'Aristotle/Landau/main/VMLInputDerive.lean',
    'Aristotle/Landau/main/CoulombConcreteTheorem42.lean'
]

for filepath in files_to_fix:
    with open(filepath, 'r') as f:
        content = f.read()

    # Theorem42
    if 'Theorem42.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun y => B y i)', 'IsSpatiallySmooth 1 (fun y => B y i)')
        content = content.replace('IsSpatiallySmooth ⊤ (fun x => f x v)', 'IsSpatiallySmooth 1 (fun x => f x v)')
    
    # Section4
    if 'Section4.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun x => f x v)', 'IsSpatiallySmooth 1 (fun x => f x v)')
        content = content.replace('IsSpatiallySmooth ⊤ (fun x => Real.log (f x v))', 'IsSpatiallySmooth 1 (fun x => Real.log (f x v))')

    # Section5
    if 'Section5.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ a', 'IsSpatiallySmooth 2 a')
        content = content.replace('IsSpatiallySmooth ⊤ (fun y => b y j)', 'IsSpatiallySmooth 2 (fun y => b y j)')
        content = content.replace('IsSpatiallySmooth ⊤ c', 'IsSpatiallySmooth 2 c')
        content = content.replace('IsSpatiallySmooth ⊤ (fun y => dotProduct (b y) v)', 'IsSpatiallySmooth 1 (fun y => dotProduct (b y) v)')
        content = content.replace('IsSpatiallySmooth ⊤ (fun y => c y * normSq v)', 'IsSpatiallySmooth 1 (fun y => c y * normSq v)')
        content = content.replace('IsSpatiallySmooth ⊤\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)', 'IsSpatiallySmooth 1\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)')
        content = content.replace('FlatTorus3.hDiff_of_le _ (by decide) ha', 'FlatTorus3.hDiff_of_le _ (by decide) ha') # keep correct but apply 2 -> 1
    
    # Section7
    if 'Section7.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun x => f x v)', 'IsSpatiallySmooth 1 (fun x => f x v)')
        content = content.replace('IsSpatiallySmooth ⊤ a₀', 'IsSpatiallySmooth 2 a₀')
    
    # Section8
    if 'Section8.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun x =>', 'IsSpatiallySmooth 1 (fun x =>')

    # VMLInputDerive
    if 'VMLInputDerive.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun x =>\n      FlatTorus3.gradX (fun y => p.b_loc y j) x i)', 'IsSpatiallySmooth 1 (fun x =>\n      FlatTorus3.gradX (fun y => p.b_loc y j) x i)')
        content = content.replace('IsSpatiallySmooth ⊤', 'IsSpatiallySmooth 2')

    # CoulombConcrete
    if 'CoulombConcreteTheorem42.lean' in filepath:
        content = content.replace('IsSpatiallySmooth ⊤ (fun x => f x v)', 'IsSpatiallySmooth 1 (fun x => f x v)')

    with open(filepath, 'w') as f:
        f.write(content)

