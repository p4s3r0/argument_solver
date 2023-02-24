class ArgumentWasAddedBefore(Exception):
    def __init__(self):
        super().__init__("add_argument: Argument was added before.")

class ArgumentWasNotAddedBefore(Exception):
    def __init__(self):
        super().__init__("del_argument: Argument was NOT added before.")

class AttackWasNotRegistered(Exception):
    def __init__(self):
        super().__init__("del_attack: Attack was not registered.")

# if attack is added twice, ignore the second one

class WitnessCallBeforeCredSkeptCall(Exception):
    def __init__(self):
        super().__init__("extract_witness: Call before solve_cred or solve_skept was called.")

class WrongArgumentationSet(Exception):
    def __init__(self):
        super().__init__("init_solver: sigma has to be CO/ST/PR")

class LibraryWasRunAsMain(Exception):
    def __init__(self):
        super().__init__("Library was run as main.")


class ParseError(Exception):
    def __init__(self):
        super().__init__("Parser: There was an unexpected parse error.")
