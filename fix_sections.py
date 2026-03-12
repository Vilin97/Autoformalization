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
    content = content.replace('hDiff_logfv', 'hDiff_logfv')  # ensure var name is fixed
    
    # Section 5
    content = content.replace('hGradChainExp _ hexp_arg_diff', 'hGradChainExp _ (hexp_arg_diff.of_le (by decide))')
    
    # Section 6
    content = content.replace('hCurlIntZero ss.B ss.b₀ ss.hDiff_B', 'hCurlIntZero ss.B ss.b₀ (fun i => (ss.hDiff_B i).of_le (by decide))')

    # TorusIntegration
    content = content.replace('hd.of_le (by decide)', 'hd.of_le (by decide)')
    content = content.replace('le_top', '(by decide)')

    with open(filepath, 'w') as f:
        f.write(content)
