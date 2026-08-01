#!/usr/bin/env python3
"""
Generate an HTML table showing which axioms are satisfied/failed by which voting rules.

This script parses the SocialChoiceLean project and creates a comprehensive table.

Usage:
    python generate_axiom_table.py                    # Current state
    python generate_axiom_table.py --compare-to COMMIT  # Theorems from historical commit
    python generate_axiom_table.py --compare-to "2026-01-13 22:00"  # Theorems from date
"""

import os
import re
import subprocess
import argparse
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Optional

# ============================================================================
# Configuration
# ============================================================================

PROJECT_ROOT = Path(__file__).parent
SOCIAL_CHOICE_DIR = PROJECT_ROOT / "SocialChoice"

# ============================================================================
# Git helpers
# ============================================================================

def resolve_commit(commit_spec: str) -> str:
    """Resolve a commit spec (hash, date, etc.) to a commit hash."""
    # Try as a date first
    try:
        result = subprocess.run(
            ["git", "rev-list", "-n", "1", f"--before={commit_spec}", "HEAD"],
            capture_output=True, text=True, check=True, cwd=PROJECT_ROOT
        )
        if result.stdout.strip():
            return result.stdout.strip()
    except subprocess.CalledProcessError:
        pass

    # Try as a commit hash/ref
    try:
        result = subprocess.run(
            ["git", "rev-parse", commit_spec],
            capture_output=True, text=True, check=True, cwd=PROJECT_ROOT
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        raise ValueError(f"Could not resolve commit: {commit_spec}")

def get_file_content_at_commit(file_path: str, commit: str) -> Optional[str]:
    """Get file content at a specific commit, or None if file didn't exist."""
    try:
        result = subprocess.run(
            ["git", "show", f"{commit}:{file_path}"],
            capture_output=True, text=True, check=True, cwd=PROJECT_ROOT
        )
        return result.stdout
    except subprocess.CalledProcessError:
        return None

def list_files_at_commit(commit: str, pattern: str = "SocialChoice/**/*.lean") -> list[str]:
    """List files matching pattern at a specific commit."""
    try:
        result = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", commit],
            capture_output=True, text=True, check=True, cwd=PROJECT_ROOT
        )
        files = result.stdout.strip().split('\n')
        import fnmatch
        return [f for f in files if fnmatch.fnmatch(f, pattern)]
    except subprocess.CalledProcessError:
        return []

# ============================================================================
# Data structures
# ============================================================================

@dataclass
class Axiom:
    name: str
    display_name: str
    file_path: str

@dataclass
class Rule:
    name: str
    display_name: str
    file_path: str
    family: Optional[str] = None
    is_scoring_rule: bool = False
    is_scoring_elimination: bool = False

@dataclass
class Theorem:
    name: str
    rule: str
    axiom: str
    satisfies: bool  # True = satisfies, False = fails
    file_path: str
    line_number: int
    is_derived: bool = False  # True if proven in Derived.lean

# ============================================================================
# Parsing functions
# ============================================================================

def normalize_name(name: str) -> str:
    """Convert camelCase or PascalCase to snake_case for matching."""
    # Insert underscore before uppercase letters and convert to lowercase
    s = re.sub(r'([a-z])([A-Z])', r'\1_\2', name)
    return s.lower()

def to_display_name(name: str) -> str:
    """Convert snake_case or camelCase to readable display name."""
    # Handle camelCase
    name = re.sub(r'([a-z])([A-Z])', r'\1 \2', name)
    # Handle snake_case
    name = name.replace('_', ' ')
    # Capitalize each word
    return name.title()

def parse_axioms() -> dict[str, Axiom]:
    """Parse axiom definitions tagged with @[scAxiom] from SocialChoice/."""
    axioms = {}

    # Pattern to match @[scAxiom] attribute (possibly with other attributes)
    # followed by a definition on the next non-empty line
    attr_pattern = re.compile(r'@\[.*?scAxiom.*?\]')
    def_pattern = re.compile(r'^(?:noncomputable\s+)?def\s+([A-Za-z][A-Za-z0-9_]*)')

    for lean_file in SOCIAL_CHOICE_DIR.rglob("*.lean"):
        content = lean_file.read_text()
        lines = content.split('\n')

        i = 0
        while i < len(lines):
            line = lines[i]
            # Check if line contains @[scAxiom]
            if attr_pattern.search(line):
                # Look for the definition on this line or subsequent lines
                # (attributes can be on the same line as def, or on preceding lines)
                def_match = def_pattern.search(line)
                if def_match:
                    name = def_match.group(1)
                else:
                    # Look at subsequent lines for the definition
                    for j in range(i + 1, min(i + 5, len(lines))):
                        # Skip empty lines and additional attribute lines
                        if lines[j].strip() == '' or lines[j].strip().startswith('@['):
                            continue
                        def_match = def_pattern.match(lines[j])
                        if def_match:
                            name = def_match.group(1)
                            break
                    else:
                        i += 1
                        continue

                axioms[normalize_name(name)] = Axiom(
                    name=name,
                    display_name=to_display_name(name),
                    file_path=str(lean_file.relative_to(PROJECT_ROOT))
                )
            i += 1

    del axioms["tops_only"]
    del axioms["margin_based"]
    del axioms["singleton_positive_involvement"]
    del axioms["independence_of_universally_least_preferred"]

    return axioms

def parse_rules() -> dict[str, Rule]:
    """Parse voting rule definitions tagged with @[scRule] from SocialChoice/."""
    rules = {}
    rules_dir = SOCIAL_CHOICE_DIR / "Rules"

    if not rules_dir.exists():
        return rules

    # Pattern to match @[scRule] attribute (possibly with other attributes)
    attr_pattern = re.compile(r'@\[.*?scRule.*?\]')
    def_pattern = re.compile(r'^(?:noncomputable\s+)?def\s+([a-zA-Z][a-zA-Z0-9_]*)')

    for lean_file in rules_dir.rglob("*.lean"):
        content = lean_file.read_text()
        relative_path = str(lean_file.relative_to(PROJECT_ROOT))
        lines = content.split('\n')

        # Determine family based on path
        family = None
        is_scoring_rule = False
        is_scoring_elimination = False

        if "ScoringRules" in relative_path:
            is_scoring_rule = True
            family = "Scoring Rules"
        elif "ScoringElimination" in relative_path:
            is_scoring_elimination = True
            family = "Scoring Elimination Rules"
        elif "Minimax" in relative_path:
            family = "Condorcet Methods"
        elif "Black" in relative_path:
            family = "Condorcet Methods"
        elif "SplitCycle" in relative_path:
            family = "Condorcet Methods"
        elif "Schulze" in relative_path:
            family = "Condorcet Methods"
        elif "DefensibleSet" in relative_path:
            family = "Condorcet Methods"
        elif "Nanson" in relative_path:
            family = "Condorcet Methods"
        elif "Copeland" in relative_path:
            family = "Condorcet Methods"
        elif "TopCycle" in relative_path:
            family = "Condorcet Methods"
        elif "UncoveredSet" in relative_path:
            family = "Condorcet Methods"
        elif "River" in relative_path:
            # family = "Condorcet Methods"
            continue
        elif "PluralityWithRunoff" in relative_path:
            family = "Runoff"

        i = 0
        while i < len(lines):
            line = lines[i]
            # Check if line contains @[scRule]
            if attr_pattern.search(line):
                # Look for the definition on this line or subsequent lines
                def_match = def_pattern.search(line)
                if def_match:
                    name = def_match.group(1)
                else:
                    # Look at subsequent lines for the definition
                    for j in range(i + 1, min(i + 5, len(lines))):
                        # Skip empty lines and additional attribute lines
                        if lines[j].strip() == '' or lines[j].strip().startswith('@['):
                            continue
                        def_match = def_pattern.match(lines[j])
                        if def_match:
                            name = def_match.group(1)
                            break
                    else:
                        i += 1
                        continue

                normalized = normalize_name(name)
                display_name = to_display_name(name)
                if name == "instantRunoffVoting":
                    display_name = "IRV"
                if name == "pluralityWithRunoff":
                    display_name = "Pl. Runoff"
                rules[normalized] = Rule(
                    name=name,
                    display_name=display_name,
                    file_path=relative_path,
                    family=family,
                    is_scoring_rule=is_scoring_rule,
                    is_scoring_elimination=is_scoring_elimination
                )
            i += 1

    return rules

def parse_theorems(axioms: dict[str, Axiom], rules: dict[str, Rule], commit: Optional[str] = None) -> list[Theorem]:
    """Parse theorems connecting rules to axioms.

    If commit is specified, reads files from that git commit instead of the filesystem.
    """
    theorems = []

    # Rule name aliases for matching
    rule_aliases = {
        'irv': 'instant_runoff_voting',
        'split_cycle': 'split_cycle',
        'splitcycle': 'split_cycle',
    }

    # Axiom name aliases (theorem name -> canonical axiom key)
    axiom_aliases = {
        'pareto': 'pareto_efficiency',
        'condorcet': 'condorcet_consistency',
        'condorcet_loser': 'condorcet_loser_criterion',
        'anonymous': 'anonymity',
        'neutral': 'neutrality',
        'monotone': 'monotonicity',
    }

    # Build a lookup for normalized rule names
    rule_lookup = {}
    for rule_key in rules:
        rule_lookup[rule_key] = rule_key
        # Also add without underscores
        rule_lookup[rule_key.replace('_', '')] = rule_key

    # Add aliases
    for alias, canonical in rule_aliases.items():
        if canonical in rules:
            rule_lookup[alias] = canonical
            rule_lookup[alias.replace('_', '')] = canonical

    # Get list of files to process
    if commit:
        file_paths = list_files_at_commit(commit, "SocialChoice/**/*.lean")
        def read_file(path):
            return get_file_content_at_commit(path, commit)
    else:
        file_paths = [str(f.relative_to(PROJECT_ROOT)) for f in SOCIAL_CHOICE_DIR.rglob("*.lean")]
        def read_file(path):
            return (PROJECT_ROOT / path).read_text()

    for relative_path in file_paths:
        content = read_file(relative_path)
        if content is None:
            continue

        lines = content.split('\n')
        for line_num, line in enumerate(lines, 1):
            # Match theorem declarations
            theorem_match = re.match(
                r'^theorem\s+([a-zA-Z][a-zA-Z0-9_]*)\s*',
                line
            )
            if not theorem_match:
                continue

            theorem_name = theorem_match.group(1)
            normalized_theorem = normalize_name(theorem_name)

            # Try to find rule name at start of theorem
            matched_rule = None
            matched_rule_len = 0

            for rule_variant, canonical_rule in rule_lookup.items():
                if normalized_theorem.startswith(rule_variant + '_') or normalized_theorem.startswith(rule_variant.replace('_', '') + '_'):
                    if len(rule_variant) > matched_rule_len:
                        matched_rule = canonical_rule
                        matched_rule_len = len(rule_variant)

            if not matched_rule:
                continue

            # Extract remainder after rule name
            # Handle both snake_case and no-underscore variants
            remainder = normalized_theorem[matched_rule_len:]
            if remainder.startswith('_'):
                remainder = remainder[1:]

            # Check for negative (not) pattern
            is_negative = False
            if remainder.startswith('not_'):
                is_negative = True
                remainder = remainder[4:]

            # Try to match axiom
            matched_axiom = None

            # First check aliases
            for alias, canonical in axiom_aliases.items():
                if remainder == alias: # or remainder.startswith(alias + '_'):
                    if canonical in axioms:
                        matched_axiom = canonical
                        break

            # Then try direct matches
            if not matched_axiom:
                for axiom_key in axioms:
                    # Try exact match first
                    if remainder == axiom_key:
                        matched_axiom = axiom_key
                        break
                    # Try prefix match
                    if remainder.startswith(axiom_key + '_') or remainder.startswith(axiom_key.replace('_', '') + '_'):
                        if matched_axiom is None or len(axiom_key) > len(matched_axiom):
                            matched_axiom = axiom_key
                    # Try without underscores
                    if remainder == axiom_key.replace('_', ''):
                        matched_axiom = axiom_key
                        break
                    if remainder.startswith(axiom_key.replace('_', '')):
                        if matched_axiom is None or len(axiom_key) > len(matched_axiom):
                            matched_axiom = axiom_key

            if matched_axiom:
                theorems.append(Theorem(
                    name=theorem_name,
                    rule=matched_rule,
                    axiom=matched_axiom,
                    satisfies=not is_negative,
                    file_path=relative_path,
                    line_number=line_num,
                    is_derived='Derived.lean' in relative_path
                ))
                continue

            # Try reverse pattern: axiom_rule (e.g., non_clone_choice_ind_clones_split_cycle)
            for axiom_key in axioms:
                axiom_variants = [axiom_key, axiom_key.replace('_', '')]
                for axiom_variant in axiom_variants:
                    if normalized_theorem.startswith(axiom_variant + '_'):
                        remainder = normalized_theorem[len(axiom_variant) + 1:]
                        # Check for rule at end
                        for rule_variant, canonical_rule in rule_lookup.items():
                            if remainder == rule_variant or remainder.endswith('_' + rule_variant):
                                theorems.append(Theorem(
                                    name=theorem_name,
                                    rule=canonical_rule,
                                    axiom=axiom_key,
                                    satisfies=True,  # Reverse pattern typically means satisfies
                                    file_path=relative_path,
                                    line_number=line_num,
                                    is_derived='Derived.lean' in relative_path
                                ))
                                break

    return theorems

# ============================================================================
# HTML generation
# ============================================================================

def generate_html(axioms: dict[str, Axiom], rules: dict[str, Rule],
                  theorems: list[Theorem], axioms_to_show: Optional[set[str]] = None) -> str:
    """Generate the HTML table.

    If axioms_to_show is provided, only those axioms will be displayed (useful for
    historical comparisons where we want to show current axioms but historical data).
    """

    # Build the results matrix
    results = defaultdict(dict)  # results[axiom][rule] = (satisfies, theorem)

    for theorem in theorems:
        key = (theorem.axiom, theorem.rule)
        if theorem.axiom in results and theorem.rule in results[theorem.axiom]:
            existing = results[theorem.axiom][theorem.rule]
            # Prefer fails over satisfies (more definitive)
            if not theorem.satisfies and existing[0]:
                # New is fails, existing is satisfies -> prefer new
                results[theorem.axiom][theorem.rule] = (theorem.satisfies, theorem)
            elif theorem.satisfies and not existing[0]:
                # New is satisfies, existing is fails -> keep existing
                continue
            elif 'via' in theorem.name and 'via' not in existing[1].name:
                # Prefer specific over generic
                continue
        else:
            results[theorem.axiom][theorem.rule] = (theorem.satisfies, theorem)

    # Organize rules by family
    families = defaultdict(list)
    for rule_key, rule in sorted(rules.items(), key=lambda x: (x[1].family or 'ZZZ', x[0])):
        if rule.family:
            families[rule.family].append(rule_key)
        else:
            families['Other'].append(rule_key)

    # Define family order
    family_order = [
        "Scoring Rules",
        "Runoff",
        "Scoring Elimination Rules",
        "Condorcet Methods",
        "Other"
    ]

    # Sort axioms for display
    axiom_order = [
        'anonymity', 'neutrality',
        'pareto_efficiency', 'unanimity',
        'condorcet_criterion', 'condorcet_consistency',
        'condorcet_loser_criterion', 'condorcet_loser_avoidance',
        'smith_criterion',
        'majority_criterion', 'majority_loser_criterion', 'mutual_majority_criterion',
        'independence_of_clones', 'independence_of_losers',
        'independence_of_dominated', 'independence_of_universally_least_preferred',
        'reversal_symmetry', 'singleton_reversal_symmetry',
        'monotonicity',
        'positive_involvement', 'negative_involvement',
        'strong_participation', 'weak_participation',
        'strong_kelly_participation', 'weak_kelly_participation',
        'strong_fishburn_participation', 'weak_fishburn_participation',
        'optimist_participation', 'pessimist_participation',
        'resolute_participation',
        'reinforcement', 'subset_reinforcement',
    ]

    families["Scoring Elimination Rules"].reverse()

    sorted_axioms = []
    for ax in axiom_order:
        if ax in axioms:
            sorted_axioms.append(ax)
    for ax in sorted(axioms.keys()):
        if ax not in sorted_axioms:
            sorted_axioms.append(ax)

    # Build ordered list of rules with families
    ordered_rules = []
    for family in family_order:
        if family in families:
            for rule_key in families[family]:
                ordered_rules.append((rule_key, family))

    # Generate HTML
    html = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>SocialChoiceLean: Axiom Satisfaction Table</title>
    <style>
        * {
            box-sizing: border-box;
        }
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
            margin: 20px;
            background: #f5f5f5;
        }
        h1 {
            color: #333;
            margin-bottom: 10px;
        }
        .controls {
            margin-bottom: 20px;
        }
        button {
            background: #4CAF50;
            color: white;
            padding: 10px 20px;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-size: 14px;
            margin-right: 10px;
        }
        button:hover {
            background: #45a049;
        }
        .table-container {
            overflow-x: auto;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        table {
            border-collapse: collapse;
            width: 100%;
            min-width: 800px;
        }
        th, td {
            border: 1px solid #ddd;
            padding: 8px 12px;
            text-align: center;
            font-size: 13px;
        }
        th {
            background: #f8f9fa;
            font-weight: 600;
            position: sticky;
            top: 0;
        }
        th.family-header {
            background: #e9ecef;
            font-weight: 700;
        }
        th.rule-header {
            background: #f8f9fa;
            font-size: 12px;
            min-width: 80px;
        }
        th.axiom-header {
            text-align: left;
            background: #f8f9fa;
            position: sticky;
            left: 0;
            z-index: 1;
        }
        td.axiom-cell {
            text-align: left;
            font-weight: 500;
            background: white;
            position: sticky;
            left: 0;
            z-index: 1;
        }
        .satisfied {
            background: #d4edda;
            color: #155724;
        }
        /*.satisfied.derived {
            background: #e8f5e9;
            color: #2e7d32;
            opacity: 0.85;
        }*/
        .failed {
            background: #f8d7da;
            color: #721c24;
        }
        /*.failed.derived {
            background: #ffebee;
            color: #b71c1c;
            opacity: 0.85;
        }*/
        .unknown {
            background: #f5f5f5;
            color: #6c757d;
        }
        .checkmark {
            font-size: 16px;
        }
        .legend {
            margin-top: 20px;
            padding: 15px;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
        .legend h3 {
            margin-top: 0;
            margin-bottom: 10px;
        }
        .legend-item {
            display: inline-block;
            margin-right: 20px;
            padding: 5px 10px;
            border-radius: 4px;
        }
        td a {
            text-decoration: none;
            color: inherit;
        }
        td a:hover {
            text-decoration: underline;
        }
        .tooltip {
            position: relative;
        }
        .tooltip:hover::after {
            content: attr(data-tooltip);
            position: absolute;
            bottom: 100%;
            left: 50%;
            transform: translateX(-50%);
            background: #333;
            color: white;
            padding: 5px 10px;
            border-radius: 4px;
            font-size: 11px;
            white-space: nowrap;
            z-index: 100;
        }
        .stats {
            margin-top: 20px;
            padding: 15px;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }
    </style>
</head>
<body>
    <h1>SocialChoiceLean: Axiom Satisfaction Table</h1>
    <p>Generated from the <a href="https://github.com/DominikPeters/SocialChoiceLean">SocialChoiceLean</a> Lean formalization project.</p>

    <div class="controls">
        <button onclick="transposeTable()">Transpose Table</button>
    </div>

    <div class="table-container">
        <table id="axiomTable">
'''

    # Count rules per family for colspan
    family_counts = defaultdict(int)
    for rule_key, family in ordered_rules:
        family_counts[family] += 1

    # Table header - family row
    html += '            <thead>\n'
    html += '                <tr>\n'
    html += '                    <th class="axiom-header"></th>\n'

    current_family = None
    for rule_key, family in ordered_rules:
        if family != current_family:
            count = family_counts[family]
            html += f'                    <th class="family-header" colspan="{count}">{family}</th>\n'
            current_family = family

    html += '                </tr>\n'

    # Table header - rule names row
    html += '                <tr>\n'
    html += '                    <th class="axiom-header">Axiom</th>\n'

    for rule_key, family in ordered_rules:
        rule = rules[rule_key]
        html += f'                    <th class="rule-header">{rule.display_name}</th>\n'

    html += '                </tr>\n'
    html += '            </thead>\n'

    # Table body
    html += '            <tbody>\n'

    for axiom_key in sorted_axioms:
        # Skip axioms with no results (use axioms_to_show if provided, otherwise check results)
        if axioms_to_show is not None:
            if axiom_key not in axioms_to_show:
                continue
        elif not results.get(axiom_key):
            continue
        axiom = axioms[axiom_key]
        html += '                <tr>\n'
        html += f'                    <td class="axiom-cell">{axiom.display_name}</td>\n'

        for rule_key, family in ordered_rules:
            if axiom_key in results and rule_key in results[axiom_key]:
                satisfies, theorem = results[axiom_key][rule_key]
                derived_class = " derived" if theorem.is_derived else ""
                github_url = f"https://github.com/DominikPeters/SocialChoiceLean/blob/master/{theorem.file_path}#L{theorem.line_number}"
                if satisfies:
                    tooltip = f"{theorem.name} in {theorem.file_path}:{theorem.line_number}"
                    html += f'                    <td class="satisfied tooltip{derived_class}" data-tooltip="{tooltip}"><a href="{github_url}" target="_blank"><span class="checkmark">&#10004;</span></a></td>\n'
                else:
                    tooltip = f"{theorem.name} in {theorem.file_path}:{theorem.line_number}"
                    html += f'                    <td class="failed tooltip{derived_class}" data-tooltip="{tooltip}"><a href="{github_url}" target="_blank"><span class="checkmark">&#10008;</span></a></td>\n'
            else:
                html += '                    <td class="unknown">-</td>\n'

        html += '                </tr>\n'

    html += '            </tbody>\n'
    html += '        </table>\n'
    html += '    </div>\n'

    # Legend
    html += '''
    <div class="legend">
        <h3>Legend</h3>
        <span class="legend-item satisfied"><span class="checkmark">&#10004;</span> Axiom satisfied (proved)</span>
        <span class="legend-item failed"><span class="checkmark">&#10008;</span> Axiom failed (proved)</span>
        <span class="legend-item unknown">- Unknown / not yet formalized</span>
    </div>
'''

    # Statistics
    # total_cells = len(sorted_axioms) * len(ordered_rules)
    # satisfied_count = sum(1 for ax in results for r in results[ax] if results[ax][r][0])
    # failed_count = sum(1 for ax in results for r in results[ax] if not results[ax][r][0])

    # html += f'''
    #     <div class="stats">
    #         <h3>Statistics</h3>
    #         <p>Total axiom-rule pairs: {total_cells}</p>
    #         <p>Proved satisfied: {satisfied_count} ({100*satisfied_count/total_cells:.1f}%)</p>
    #         <p>Proved failed: {failed_count} ({100*failed_count/total_cells:.1f}%)</p>
    #         <p>Unknown: {total_cells - satisfied_count - failed_count} ({100*(total_cells - satisfied_count - failed_count)/total_cells:.1f}%)</p>
    #     </div>
    # '''

    # JavaScript for transpose
    html += '''
    <script>
        let isTransposed = false;

        function transposeTable() {
            const table = document.getElementById('axiomTable');
            const rows = Array.from(table.rows);

            // Get all data including headers
            const data = rows.map(row => Array.from(row.cells).map(cell => ({
                html: cell.innerHTML,
                className: cell.className,
                colspan: cell.colSpan,
                rowspan: cell.rowSpan,
                tooltip: cell.dataset.tooltip || ''
            })));

            // Clear table
            table.innerHTML = '';

            if (!isTransposed) {
                // Transpose: swap rows and columns
                // Skip the family header row (index 0) for now
                const maxCols = Math.max(...data.map(row => row.length));

                // Create new header
                const thead = table.createTHead();
                const headerRow = thead.insertRow();
                const th = document.createElement('th');
                th.className = 'rule-header';
                th.textContent = 'Rule';
                headerRow.appendChild(th);

                // Add axiom names as column headers (from first column of data rows, starting from row 2)
                for (let i = 2; i < data.length; i++) {
                    const th = document.createElement('th');
                    th.className = 'axiom-header';
                    th.innerHTML = data[i][0].html;
                    headerRow.appendChild(th);
                }

                // Create body with rules as rows
                const tbody = table.createTBody();

                // Get rule names from header row (index 1)
                for (let j = 1; j < data[1].length; j++) {
                    const row = tbody.insertRow();

                    // Rule name cell
                    const ruleCell = row.insertCell();
                    ruleCell.className = 'rule-header';
                    ruleCell.innerHTML = data[1][j].html;

                    // Axiom result cells
                    for (let i = 2; i < data.length; i++) {
                        const cell = row.insertCell();
                        if (data[i][j]) {
                            cell.innerHTML = data[i][j].html;
                            cell.className = data[i][j].className;
                            if (data[i][j].tooltip) {
                                cell.dataset.tooltip = data[i][j].tooltip;
                            }
                        } else {
                            cell.innerHTML = '-';
                            cell.className = 'unknown';
                        }
                    }
                }
            } else {
                // Restore original - reload page is simplest
                location.reload();
                return;
            }

            isTransposed = !isTransposed;
        }
    </script>
</body>
</html>
'''

    return html

# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Generate axiom satisfaction table for SocialChoiceLean"
    )
    parser.add_argument(
        "--compare-to",
        dest="compare_to",
        help="Show theorems from a historical commit (hash or date like '2026-01-13 22:00')"
    )
    parser.add_argument(
        "-o", "--output",
        dest="output",
        help="Output file path (default: axiom_table.html)"
    )
    args = parser.parse_args()

    # Resolve the compare-to commit if specified
    compare_commit = None
    if args.compare_to:
        print(f"Resolving commit for: {args.compare_to}")
        compare_commit = resolve_commit(args.compare_to)
        print(f"  Using commit: {compare_commit[:12]}")

    print("Parsing axioms (from current HEAD)...")
    axioms = parse_axioms()
    print(f"  Found {len(axioms)} axioms")
    for ax in sorted(axioms.keys()):
        print(f"    - {axioms[ax].display_name}")

    print("\nParsing rules (from current HEAD)...")
    rules = parse_rules()
    print(f"  Found {len(rules)} rules")
    for r in sorted(rules.keys()):
        rule = rules[r]
        family_str = f" [{rule.family}]" if rule.family else ""
        print(f"    - {rule.display_name}{family_str}")

    # When comparing to a historical commit, we need to know which axioms
    # have results in the CURRENT state (to show them even if empty historically)
    axioms_to_show = None
    if compare_commit:
        print("\nParsing current theorems (to determine which axioms to show)...")
        current_theorems = parse_theorems(axioms, rules, commit=None)
        axioms_to_show = {t.axiom for t in current_theorems}
        print(f"  {len(axioms_to_show)} axioms have results in current state")

        print(f"\nParsing historical theorems (from commit {compare_commit[:12]})...")
        theorems = parse_theorems(axioms, rules, commit=compare_commit)
    else:
        print("\nParsing theorems...")
        theorems = parse_theorems(axioms, rules, commit=None)

    print(f"  Found {len(theorems)} theorem connections")

    # Group by satisfies/fails
    satisfies = [t for t in theorems if t.satisfies]
    fails = [t for t in theorems if not t.satisfies]
    print(f"    - Satisfies: {len(satisfies)}")
    print(f"    - Fails: {len(fails)}")

    print("\nGenerating HTML...")
    html = generate_html(axioms, rules, theorems, axioms_to_show=axioms_to_show)

    output_path = Path(args.output) if args.output else PROJECT_ROOT / "axiom_table.html"
    output_path.write_text(html)
    print(f"  Written to {output_path}")

    print("\nDone!")

if __name__ == "__main__":
    main()
