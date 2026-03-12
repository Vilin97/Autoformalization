import os

files_to_fix = [
    'Aristotle/Landau/main/Section4.lean',
    'Aristotle/Landau/main/Section5.lean',
    'Aristotle/Landau/main/Section6.lean',
    'Aristotle/Landau/main/TorusIntegration.lean'
]

for filepath in files_to_fix:
    with open(filepath, 'r') as f:
        content = f.read()

    # Section 4
    content = content.replace('FlatTorus3.hIBP_spatial (fun x => f x v) (fun x => Real.log (f x v)) i\n    hDiff_fv hDiff_logfv', 'FlatTorus3.hIBP_spatial (fun x => f x v) (fun x => Real.log (f x v)) i\n    (hDiff_fv.of_le (by decide)) (hDiff_logfv.of_le (by decide))')
    content = content.replace('FlatTorus3.hGradChainLog (fun y => f y v) hDiff_fv', 'FlatTorus3.hGradChainLog (fun y => f y v) (hDiff_fv.of_le (by decide))')
    content = content.replace('FlatTorus3.hGradIntZero (fun y => f y v) hDiff_fv', 'FlatTorus3.hGradIntZero (fun y => f y v) (hDiff_fv.of_le (by decide))')

    # Section 5
    content = content.replace('FlatTorus3.hGradChainExp _ (hexp_arg_diff.of_le (by decide))', 'FlatTorus3.hGradChainExp _ (hexp_arg_diff.of_le (by decide))') # ensure no double-replace issues if we re-run
    content = content.replace('hexp_arg_diff.of_le', 'hexp_arg_diff.of_le')
    
    with open(filepath, 'w') as f:
        f.write(content)
