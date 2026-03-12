import os

files = {
    'Aristotle/Landau/main/Theorem42.lean': [
        ('FlatTorus3.hDiff_continuous ⊤', 'FlatTorus3.hDiff_continuous 0'),
    ],
    'Aristotle/Landau/main/VMLStructures.lean': [
        ('FlatTorus3.IsSpatiallySmooth ⊤ (fun y => B y i)', 'FlatTorus3.IsSpatiallySmooth 1 (fun y => B y i)')
    ],
    'Aristotle/Landau/main/Section5.lean': [
        ('FlatTorus3.IsSpatiallySmooth ⊤ a', 'FlatTorus3.IsSpatiallySmooth 2 a'),
        ('FlatTorus3.IsSpatiallySmooth ⊤ (fun y => b y j)', 'FlatTorus3.IsSpatiallySmooth 2 (fun y => b y j)'),
        ('FlatTorus3.IsSpatiallySmooth ⊤ c', 'FlatTorus3.IsSpatiallySmooth 2 c'),
        ('FlatTorus3.IsSpatiallySmooth ⊤ (fun y => dotProduct (b y) v)', 'FlatTorus3.IsSpatiallySmooth 1 (fun y => dotProduct (b y) v)'),
        ('FlatTorus3.IsSpatiallySmooth ⊤ (fun y => c y * normSq v)', 'FlatTorus3.IsSpatiallySmooth 1 (fun y => c y * normSq v)'),
        ('FlatTorus3.IsSpatiallySmooth ⊤\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)', 'FlatTorus3.IsSpatiallySmooth 1\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)'),
        ('FlatTorus3.hDiff_add ⊤', 'FlatTorus3.hDiff_add 1'),
        ('FlatTorus3.hDiff_smul ⊤', 'FlatTorus3.hDiff_smul 1'),
        ('FlatTorus3.hDiff_add 2 _ _ ha (FlatTorus3.hDiff_add 1 _ _ hbv hcv)', 'FlatTorus3.hDiff_add 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) ha) (FlatTorus3.hDiff_add 1 _ _ hbv hcv)'),
    ],
    'Aristotle/Landau/main/VMLInputDerive.lean': [
        ('FlatTorus3.hDiff_grad ⊤', 'FlatTorus3.hDiff_grad 1')
    ]
}

for filepath, replacements in files.items():
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Extra fix for Section5.lean specific line 128
    if filepath == 'Aristotle/Landau/main/Section5.lean':
        content = content.replace('FlatTorus3.hDiff_add 1 _ _ ha', 'FlatTorus3.hDiff_add 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) ha)')
        content = content.replace('FlatTorus3.hDiff_smul 1 _ _ hc', 'FlatTorus3.hDiff_smul 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) hc)')
        content = content.replace('FlatTorus3.hDiff_smul 1 _ _ (hb 0)', 'FlatTorus3.hDiff_smul 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) (hb 0))')
        content = content.replace('FlatTorus3.hDiff_smul 1 _ _ (hb 1)', 'FlatTorus3.hDiff_smul 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) (hb 1))')
        content = content.replace('FlatTorus3.hDiff_smul 1 _ _ (hb 2)', 'FlatTorus3.hDiff_smul 1 _ _ (FlatTorus3.hDiff_of_le _ (by decide) (hb 2))')

    for old, new in replacements:
        content = content.replace(old, new)
        
    with open(filepath, 'w') as f:
        f.write(content)
