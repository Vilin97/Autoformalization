import os

files = {
    'Aristotle/Landau/main/Theorem42.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun y => B y i)', 'FlatTorus3.IsSpatiallySmooth 2 (fun y => B y i)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => Real.log (f x v))', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v))'),
        ('FlatTorus3.hDiff_log 1', 'FlatTorus3.hDiff_log 2'),
    ],
    'Aristotle/Landau/main/VMLStructures.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun y => B y i)', 'FlatTorus3.IsSpatiallySmooth 2 (fun y => B y i)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)'),
    ],
    'Aristotle/Landau/main/Section4.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => Real.log (f x v))', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v))'),
        ('FlatTorus3.hDiff_log 1', 'FlatTorus3.hDiff_log 2'),
    ],
    'Aristotle/Landau/main/Section5.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun y => dotProduct (b y) v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun y => dotProduct (b y) v)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun y => c y * normSq v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun y => c y * normSq v)'),
        ('FlatTorus3.IsSpatiallySmooth 1\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)', 'FlatTorus3.IsSpatiallySmooth 2\n      (fun y => a y + dotProduct (b y) v + c y * normSq v)'),
        ('FlatTorus3.hDiff_add 1', 'FlatTorus3.hDiff_add 2'),
        ('FlatTorus3.hDiff_smul 1', 'FlatTorus3.hDiff_smul 2'),
    ],
    'Aristotle/Landau/main/Section7.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)'),
        ('FlatTorus3.hDiff_log 1', 'FlatTorus3.hDiff_log 2'),
    ],
    'Aristotle/Landau/main/Section8.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x =>', 'FlatTorus3.IsSpatiallySmooth 2 (fun x =>'),
        ('FlatTorus3.hDiff_grad 1', 'FlatTorus3.hDiff_grad 2'),
    ],
    'Aristotle/Landau/main/CoulombConcreteTheorem42.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)')
    ],
    'Aristotle/Landau/main/Section2.lean': [
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => f x v)', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)'),
        ('FlatTorus3.IsSpatiallySmooth 1 (fun x => Real.log (f x v))', 'FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v))')
    ]
}

for filepath, replacements in files.items():
    if os.path.exists(filepath):
        with open(filepath, 'r') as f:
            content = f.read()
            
        for old, new in replacements:
            content = content.replace(old, new)
            
        with open(filepath, 'w') as f:
            f.write(content)
