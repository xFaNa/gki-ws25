from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Callable, Any, Set, Optional
import random
import math

Var = str
Val = int
ConstraintFunc = Callable[[Val, Val], bool]


# Constraint & CSP-Struktur

@dataclass
class BinaryConstraint:
    x: Var
    y: Var
    func: ConstraintFunc   # func(value_x, value_y) -> bool


@dataclass
class CSP:
    variables: List[Var]
    domains: Dict[Var, List[Val]]
    constraints: List[BinaryConstraint]
    neighbors: Dict[Var, Set[Var]] = field(default_factory=dict)

    def __post_init__(self):
        # Nachbarn aus Constraints ableiten
        if not self.neighbors:
            self.neighbors = {v: set() for v in self.variables}
            for c in self.constraints:
                self.neighbors[c.x].add(c.y)
                self.neighbors[c.y].add(c.x)

    def constraint_satisfied(self, var: Var, value: Val, assignment: Dict[Var, Val]) -> bool:
        """
        Prüft: ist die Belegung (var = value) konsistent mit allen Constraints
        zu bereits zugewiesenen Variablen?
        """
        for c in self.constraints:
            if c.x == var and c.y in assignment:
                if not c.func(value, assignment[c.y]):
                    return False
            elif c.y == var and c.x in assignment:
                if not c.func(assignment[c.x], value):
                    return False
        return True

    def count_conflicts(self, var: Var, value: Val, assignment: Dict[Var, Val]) -> int:
        """
        Zählt, wie viele Constraints verletzt wären, wenn var = value wäre,
        bei gegebener (evtl. inkonsistenter) Zuweisung.
        Wird für Min-Conflicts genutzt.
        """
        conflicts = 0
        for c in self.constraints:
            if c.x == var and c.y in assignment:
                if not c.func(value, assignment[c.y]):
                    conflicts += 1
            elif c.y == var and c.x in assignment:
                if not c.func(assignment[c.x], value):
                    conflicts += 1
        return conflicts

    # AC-3

    def ac3(self) -> bool:
        """
        AC-3 Algorithmus: Macht die Domänen arc-konsistent.
        Gibt False zurück, wenn eine Domäne leer wird (Unlösbarkeit).
        """
        queue: List[Tuple[Var, Var]] = []
        for c in self.constraints:
            queue.append((c.x, c.y))
            queue.append((c.y, c.x))

        while queue:
            xi, xj = queue.pop(0)
            if self.revise(xi, xj):
                if not self.domains[xi]:
                    return False
                for xk in self.neighbors[xi]:
                    if xk != xj:
                        queue.append((xk, xi))
        return True

    def revise(self, xi: Var, xj: Var) -> bool:
        """
        Versucht, Domäne von xi zu verkleinern, indem Werte entfernt werden,
        die zu keinem Wert in Domain(xj) passen.
        """
        revised = False
        # nur Constraints direkt zwischen xi und xj
        relevant = [c for c in self.constraints if (c.x == xi and c.y == xj)]
        if not relevant:
            return False

        new_domain = []
        for vx in self.domains[xi]:
            ok = False
            for vj in self.domains[xj]:
                if all(c.func(vx, vj) for c in relevant):
                    ok = True
                    break
            if ok:
                new_domain.append(vx)
            else:
                revised = True
        if revised:
            self.domains[xi] = new_domain
        return revised


# Einstein-Rätsel als CSP

def build_einstein_csp() -> CSP:
    positions = [1, 2, 3, 4, 5]

    colors = ["Rot", "Grün", "Weiß", "Gelb", "Blau"]
    nations = ["Engländer", "Spanier", "Ukrainer", "Norweger", "Japaner"]
    drinks = ["Kaffee", "Tee", "Milch", "Orangensaft", "Wasser"]
    pets = ["Hund", "Schnecken", "Fuchs", "Pferd", "Zebra"]
    smokes = ["OldGold", "Kools", "Chesterfield", "LuckyStrike", "Parliaments"]

    variables = colors + nations + drinks + pets + smokes
    domains = {v: positions.copy() for v in variables}

    # unäre Constraints direkt in die Domänen
    domains["Norweger"] = [1]   # wohnt im ersten Haus
    domains["Milch"] = [3]      # mittleres Haus
    # Grün ist rechts von Weiß -> mögliche Positionen einschränken
    domains["Weiß"] = [1, 2, 3, 4]
    domains["Grün"] = [2, 3, 4, 5]

    constraints: List[BinaryConstraint] = []

    # Hilfsfunktion All-Different pro Kategorie
    def add_all_different(group):
        for i in range(len(group)):
            for j in range(i + 1, len(group)):
                a, b = group[i], group[j]
                constraints.append(BinaryConstraint(a, b, lambda x, y: x != y))
                constraints.append(BinaryConstraint(b, a, lambda x, y: x != y))

    # All-Different für jede Kategorie
    add_all_different(colors)
    add_all_different(nations)
    add_all_different(drinks)
    add_all_different(pets)
    add_all_different(smokes)

    # kleine Helfer für Constraints
    def eq():
        return lambda x, y: x == y

    def right_of():
        # x ist direkt rechts von y: x = y + 1
        return lambda x, y: x == y + 1

    def neighbor():
        return lambda x, y: abs(x - y) == 1

    # (1) Engländer wohnt im roten Haus.
    constraints.append(BinaryConstraint("Engländer", "Rot", eq()))
    constraints.append(BinaryConstraint("Rot", "Engländer", eq()))

    # (2) Der Spanier hat einen Hund.
    constraints.append(BinaryConstraint("Spanier", "Hund", eq()))
    constraints.append(BinaryConstraint("Hund", "Spanier", eq()))

    # (3) Kaffee wird im grünen Haus getrunken.
    constraints.append(BinaryConstraint("Kaffee", "Grün", eq()))
    constraints.append(BinaryConstraint("Grün", "Kaffee", eq()))

    # (4) Der Ukrainer trinkt Tee.
    constraints.append(BinaryConstraint("Ukrainer", "Tee", eq()))
    constraints.append(BinaryConstraint("Tee", "Ukrainer", eq()))

    # (5) Das grüne Haus ist direkt rechts vom weißen Haus.
    constraints.append(BinaryConstraint("Grün", "Weiß", right_of()))

    # (6) Old-Gold-Raucher hat Schnecken.
    constraints.append(BinaryConstraint("OldGold", "Schnecken", eq()))
    constraints.append(BinaryConstraint("Schnecken", "OldGold", eq()))

    # (7) Kools im gelben Haus.
    constraints.append(BinaryConstraint("Kools", "Gelb", eq()))
    constraints.append(BinaryConstraint("Gelb", "Kools", eq()))

    # (10) Chesterfield neben Fuchs.
    constraints.append(BinaryConstraint("Chesterfield", "Fuchs", neighbor()))
    constraints.append(BinaryConstraint("Fuchs", "Chesterfield", neighbor()))

    # (11) Kools neben Pferd.
    constraints.append(BinaryConstraint("Kools", "Pferd", neighbor()))
    constraints.append(BinaryConstraint("Pferd", "Kools", neighbor()))

    # (12) Lucky Strike -> Orangensaft.
    constraints.append(BinaryConstraint("LuckyStrike", "Orangensaft", eq()))
    constraints.append(BinaryConstraint("Orangensaft", "LuckyStrike", eq()))

    # (13) Japaner raucht Parliaments.
    constraints.append(BinaryConstraint("Japaner", "Parliaments", eq()))
    constraints.append(BinaryConstraint("Parliaments", "Japaner", eq()))

    # (14) Norweger wohnt neben blauem Haus.
    constraints.append(BinaryConstraint("Norweger", "Blau", neighbor()))
    constraints.append(BinaryConstraint("Blau", "Norweger", neighbor()))

    return CSP(variables, domains, constraints)


# -------------------- Backtracking Search + Heuristiken --------------------

@dataclass
class BTStats:
    nodes: int = 0
    failures: int = 0


def select_unassigned_variable(csp: CSP,
                               assignment: Dict[Var, Val],
                               use_mrv: bool,
                               use_degree: bool) -> Var:
    unassigned = [v for v in csp.variables if v not in assignment]

    if not use_mrv:
        # Basis-Algorithmus einfach erste noch nicht belegte Variable
        return unassigned[0]

    # MRV Variable mit der kleinsten Anzahl zulässiger Werte
    def num_legal(v):
        count = 0
        for val in csp.domains[v]:
            if csp.constraint_satisfied(v, val, assignment):
                count += 1
        return count

    mrv_vals = [(v, num_legal(v)) for v in unassigned]
    min_domain = min(c for _, c in mrv_vals)
    candidates = [v for v, c in mrv_vals if c == min_domain]

    if not use_degree or len(candidates) == 1:
        return candidates[0]

    # Gradheuristik bei Gleichstand Variable mit den meisten Nachbarn wählen
    def degree(v):
        return sum(1 for n in csp.neighbors[v] if n not in assignment)

    candidates.sort(key=lambda v: -degree(v))
    return candidates[0]


def order_values(csp: CSP, var: Var, assignment: Dict[Var, Val]) -> List[Val]:
    # einfache Reihenfolge (keine LCV-Heuristik)
    return list(csp.domains[var])


def backtracking_search(csp: CSP, use_mrv=False, use_degree=False) -> Tuple[Optional[Dict[Var, Val]], BTStats]:
    stats = BTStats()

    def backtrack(assignment: Dict[Var, Val]) -> Optional[Dict[Var, Val]]:
        stats.nodes += 1
        if len(assignment) == len(csp.variables):
            return assignment

        var = select_unassigned_variable(csp, assignment, use_mrv, use_degree)

        for value in order_values(csp, var, assignment):
            if csp.constraint_satisfied(var, value, assignment):
                assignment[var] = value
                result = backtrack(assignment)
                if result is not None:
                    return result
                assignment.pop(var)

        stats.failures += 1
        return None

    result = backtrack({})
    return result, stats


# Min-Conflicts

def min_conflicts(csp: CSP,
                  max_steps=10000,
                  restarts=10) -> Tuple[Optional[Dict[Var, Val]], int, int]:
    """
    Min-Conflicts mit zufälligem Start und optionalen Restarts.
    Gibt (Lösung oder None, verwendete Restarts, Schritte im letzten Lauf) zurück.
    """

    def conflicted_vars(assignment):
        return [v for v in csp.variables
                if csp.count_conflicts(v, assignment[v], assignment) > 0]

    for r in range(restarts):
        # zufällige Startzuweisung (evtl. inkonsistent)
        assignment = {v: random.choice(csp.domains[v]) for v in csp.variables}

        for step in range(max_steps):
            bad = conflicted_vars(assignment)
            if not bad:
                return assignment, r, step

            var = random.choice(bad)
            best_val = None
            best_conf = math.inf
            for val in csp.domains[var]:
                conf = csp.count_conflicts(var, val, assignment)
                if conf < best_conf:
                    best_conf = conf
                    best_val = val
            assignment[var] = best_val

    return None, restarts, max_steps


def pretty_solution(solution: Dict[Var, Val]):
    houses = {i: {"Farbe": None, "Nation": None, "Getränk": None,
                  "Tier": None, "Zigaretten": None}
              for i in range(1, 6)}

    colors = ["Rot", "Grün", "Weiß", "Gelb", "Blau"]
    nations = ["Engländer", "Spanier", "Ukrainer", "Norweger", "Japaner"]
    drinks = ["Kaffee", "Tee", "Milch", "Orangensaft", "Wasser"]
    pets = ["Hund", "Schnecken", "Fuchs", "Pferd", "Zebra"]
    smokes = ["OldGold", "Kools", "Chesterfield", "LuckyStrike", "Parliaments"]

    for var, pos in solution.items():
        if var in colors:
            houses[pos]["Farbe"] = var
        elif var in nations:
            houses[pos]["Nation"] = var
        elif var in drinks:
            houses[pos]["Getränk"] = var
        elif var in pets:
            houses[pos]["Tier"] = var
        elif var in smokes:
            houses[pos]["Zigaretten"] = var

    for i in range(1, 6):
        print(f"Haus {i}: {houses[i]}")
    print()

    wasser_haus = solution["Wasser"]
    zebra_haus = solution["Zebra"]
    wasser_trinker = [n for n, p in solution.items() if p == wasser_haus and n in nations][0]
    zebra_besitzer = [n for n, p in solution.items() if p == zebra_haus and n in nations][0]
    print(f"-> Wasser trinkt: {wasser_trinker} (Haus {wasser_haus})")
    print(f"-> Zebra gehört: {zebra_besitzer} (Haus {zebra_haus})")


# -------------------- Experimente / main --------------------

if __name__ == "__main__":
    random.seed(0)

    # 1) Basis-Backtracking (ohne MRV/Grad)
    print("Backtracking (Basis)")
    csp1 = build_einstein_csp()
    sol_bt, stats_bt = backtracking_search(csp1, use_mrv=False, use_degree=False)
    print(f"Lösung gefunden: {sol_bt is not None}")
    print(f"Knoten: {stats_bt.nodes}, Fehlschläge: {stats_bt.failures}\n")

    # 2) Backtracking mit MRV + Gradheuristik
    print("Backtracking mit MRV + Gradheuristik")
    csp2 = build_einstein_csp()
    sol_mrv, stats_mrv = backtracking_search(csp2, use_mrv=True, use_degree=True)
    print(f"Lösung gefunden: {sol_mrv is not None}")
    print(f"Knoten: {stats_mrv.nodes}, Fehlschläge: {stats_mrv.failures}\n")

    # 3) AC-3 vor Backtracking
    print("AC-3 + Backtracking (mit MRV + Grad)")
    csp3 = build_einstein_csp()
    consistent = csp3.ac3()
    print(f"AC-3 konsistent: {consistent}")
    all_singleton = all(len(dom) == 1 for dom in csp3.domains.values())
    print(f"Alle Domänen einwertig nach AC-3? {all_singleton}")
    if consistent and not all_singleton:
        sol_ac3, stats_ac3 = backtracking_search(csp3, use_mrv=True, use_degree=True)
        print(f"Lösung gefunden: {sol_ac3 is not None}")
        print(f"Knoten: {stats_ac3.nodes}, Fehlschläge: {stats_ac3.failures}\n")

    # 4) Min-Conflicts
    print("Min-Conflicts")
    csp4 = build_einstein_csp()
    sol_mc, restarts, steps = min_conflicts(csp4, max_steps=5000, restarts=30)
    print(f"Lösung gefunden: {sol_mc is not None}")
    print(f"Restarts: {restarts}, Schritte im letzten Lauf: {steps}\n")

    # Beispiel-Lösung
    if sol_bt:
        print("Beispiel-Lösung (Backtracking)")
        pretty_solution(sol_bt)
