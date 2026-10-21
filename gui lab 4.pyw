import tkinter as tk
from tkinter import messagebox, filedialog
import ast
import heapq
from collections import deque

# --- Core Logic ---
GOAL_STATE = [1, 2, 3, 4, 5, 6, 7, 8, '']

def is_valid_state(state):
    # check if it's actually a list and exactly 9 elements long
    if not isinstance(state, list) or len(state) != 9:
        return False
    # converting to a set drops duplicates, so this checks for exact unique matches
    return set(state) == {1, 2, 3, 4, 5, 6, 7, 8, ''}

def get_valid_moves(state):
    # find where the blank space is right now
    blank_idx = state.index('')
    
    # quick math to get 2D coordinates (row, col) from the 1D index
    row, col = divmod(blank_idx, 3)
    
    valid_moves = {}
    # block moves that would push the blank space off the grid
    if row > 0: valid_moves['W'] = blank_idx - 3
    if col > 0: valid_moves['A'] = blank_idx - 1
    if row < 2: valid_moves['X'] = blank_idx + 3
    if col < 2: valid_moves['D'] = blank_idx + 1
    return valid_moves

def apply_move(state, move):
    valid_moves = get_valid_moves(state)
    blank_idx = state.index('')
    target_idx = valid_moves[move]
    
    # make a copy here so we don't accidentally overwrite the parent node's board
    new_state = state.copy()
    new_state[blank_idx], new_state[target_idx] = new_state[target_idx], new_state[blank_idx]
    return new_state

def is_solvable(state, goal_state):
    # check reachability before wasting time searching
    def inversions(board):
        tiles = [t for t in board if t != '']
        count = 0
        for i in range(len(tiles)):
            for j in range(i + 1, len(tiles)):
                if tiles[i] > tiles[j]:
                    count += 1
        return count
    # reachable only if both counts are even or both odd
    return inversions(state) % 2 == inversions(goal_state) % 2

# --- Unified Node Class ---
class Node:
    def __init__(self, state, parent=None, move=None, g_cost=0, h_cost=0):
        self.state = state
        self.parent = parent
        self.move = move
        self.g_cost = g_cost        # acts as 'depth' for BFS and path cost for A*
        self.h_cost = h_cost
        self.f_cost = g_cost + h_cost
        
    def __lt__(self, other):
        # REQUIRED FOR HEAPQ: tells the priority queue how to break ties
        if self.f_cost == other.f_cost:
            return self.h_cost < other.h_cost
        return self.f_cost < other.f_cost

def reconstruct_path(node):
    # walk backward from the goal to the start using each node's parent
    path = []
    moves = []
    while node is not None:
        path.append(node.state)
        if node.move:
            moves.append(node.move)
        node = node.parent
    # lists are built backwards, so flip them
    path.reverse()
    moves.reverse()
    return path, moves

# --- Search Algorithms ---
def bfs(initial_state, goal_state):
    start = Node(initial_state)
    if start.state == goal_state:
        return [start.state], [], 1
        
    # deque gives BFS a fast first-in, first-out queue
    frontier = deque([start])
    visited = {tuple(initial_state)}
    boards_examined = 0
    
    while frontier:
        # take the oldest board (front of queue)
        node = frontier.popleft()
        boards_examined += 1
        
        valid_moves = get_valid_moves(node.state)
        for move in valid_moves:
            new_state = apply_move(node.state, move)
            
            # skip boards we've already seen
            if tuple(new_state) in visited:
                continue
            visited.add(tuple(new_state))
            
            # wrap it, remembering where it came from
            child = Node(new_state, parent=node, move=move, g_cost=node.g_cost + 1)
            
            if child.state == goal_state:
                path, moves = reconstruct_path(child)
                return path, moves, boards_examined
                
            # new boards go to the back of the queue
            frontier.append(child)
            
    return None, None, boards_examined

def calculate_manhattan_distance(state, goal_state):
    # dynamic heuristic function (h_cost)
    distance = 0
    for i in range(9):
        val = state[i]
        if val != '':  # don't count the blank space
            goal_idx = goal_state.index(val)
            curr_row, curr_col = divmod(i, 3)
            goal_row, goal_col = divmod(goal_idx, 3)
            distance += abs(curr_row - goal_row) + abs(curr_col - goal_col)
    return distance

def a_star_8_puzzle(start_state, goal_state):
    h_start = calculate_manhattan_distance(start_state, goal_state)
    start_node = Node(start_state, None, None, 0, h_start)
    
    # using a priority queue (heap) stops the program from freezing
    open_list = []
    heapq.heappush(open_list, start_node)
    
    closed_list = set()
    # have to use a tuple for the key because dictionaries hate unhashable lists
    best_g = {tuple(start_state): 0}
    nodes_expanded = 0
    
    while open_list:
        # instantly grabs the lowest f_cost node without looping
        current = heapq.heappop(open_list)
        current_tuple = tuple(current.state)
        
        # skip if we already explored a cheaper version of this board
        if current_tuple in closed_list:
            continue
            
        nodes_expanded += 1
        
        if current.state == goal_state:
            path, moves = reconstruct_path(current)
            return path, moves, nodes_expanded
            
        closed_list.add(current_tuple)
        
        valid_moves = get_valid_moves(current.state)
        for move in valid_moves:
            neighbor_state = apply_move(current.state, move)
            neighbor_tuple = tuple(neighbor_state)
            
            if neighbor_tuple in closed_list:
                continue
                
            # cost of 1 slide is always 1
            new_g = current.g_cost + 1
            
            # only add to queue if it's a completely new board or we found a faster way to it
            if neighbor_tuple not in best_g or new_g < best_g[neighbor_tuple]:
                best_g[neighbor_tuple] = new_g
                h = calculate_manhattan_distance(neighbor_state, goal_state)
                child = Node(neighbor_state, current, move, new_g, h)
                heapq.heappush(open_list, child)
                
    return None, None, nodes_expanded

# --- GUI Application ---
class EightPuzzleSolverGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("8-Puzzle Auto-Solver")

        # Synthwave Color Palette
        self.bg_color = "#2b0f4c"
        self.cyan = "#00e5ff"
        self.hot_pink = "#ff0066"
        self.yellow = "#ffe600"
        self.magenta = "#cc00ff"
        self.blank_color = "#150529"
        
        self.configure(bg=self.bg_color)
        
        self.solution_path = []
        self.solution_moves = []
        self.current_step = 0
        
        arcade_font = ("Courier New", 12, "bold")
        title_font = ("Courier New", 16, "bold")
        
        # Setup UI labels
        tk.Label(self, text="INITIAL STATE:", bg=self.bg_color, fg=self.cyan, font=title_font).pack(pady=5)
        
        # setup the initial choice buttons
        self.choice_frame = tk.Frame(self, bg=self.bg_color)
        self.choice_frame.pack(pady=5)
        
        self.upload_btn = tk.Button(self.choice_frame, text="UPLOAD .TXT", bg=self.cyan, fg=self.bg_color, font=arcade_font,
                                    activebackground=self.magenta, relief="raised", bd=2, command=self.load_from_file)
        self.upload_btn.grid(row=0, column=0, padx=5)
        
        self.manual_btn = tk.Button(self.choice_frame, text="INPUT MANUALLY", bg=self.cyan, fg=self.bg_color, font=arcade_font,
                                    activebackground=self.magenta, relief="raised", bd=2, command=self.show_manual_input)
        self.manual_btn.grid(row=0, column=1, padx=5)
        
        # setup the input text box but don't pack it to the window yet
        self.input_frame = tk.Frame(self, bg=self.bg_color)
        self.input_entry = tk.Entry(self.input_frame, width=35, bg=self.blank_color, fg=self.yellow, font=arcade_font, 
                                    insertbackground=self.cyan, justify="center", bd=2, relief="solid")
        self.input_entry.insert(0, "[1, 2, 3, 4, '', 8, 5, 6, 7]")
        
        # solver buttons
        btn_frame = tk.Frame(self, bg=self.bg_color)
        btn_frame.pack(pady=5)
        
        bfs_btn = tk.Button(btn_frame, text="SOLVE (BFS)", bg=self.magenta, fg=self.yellow, font=arcade_font, 
                             activebackground=self.cyan, activeforeground=self.bg_color, relief="raised", bd=3,
                             command=self.solve_bfs)
        bfs_btn.grid(row=0, column=0, padx=5)
        
        astar_btn = tk.Button(btn_frame, text="SOLVE (A*)", bg=self.magenta, fg=self.yellow, font=arcade_font, 
                             activebackground=self.cyan, activeforeground=self.bg_color, relief="raised", bd=3,
                             command=self.solve_astar)
        astar_btn.grid(row=0, column=1, padx=5)
        
        self.status_label = tk.Label(self, text="READY. SELECT INPUT METHOD TO BEGIN.", bg=self.bg_color, fg=self.cyan, font=arcade_font)
        self.status_label.pack(pady=5)
        
        # player navigation controls
        nav_frame = tk.Frame(self, bg=self.bg_color)
        nav_frame.pack(pady=10)
        
        self.prev_btn = tk.Button(nav_frame, text="<< PREV", bg=self.cyan, fg=self.bg_color, font=arcade_font, 
                                  state=tk.DISABLED, command=self.step_prev)
        self.prev_btn.grid(row=0, column=0, padx=10)
        
        self.step_label = tk.Label(nav_frame, text="STEP 0 / 0", bg=self.bg_color, fg=self.yellow, font=arcade_font)
        self.step_label.grid(row=0, column=1, padx=10)
        
        self.next_btn = tk.Button(nav_frame, text="NEXT >>", bg=self.cyan, fg=self.bg_color, font=arcade_font, 
                                  state=tk.DISABLED, command=self.step_next)
        self.next_btn.grid(row=0, column=2, padx=10)
        
        # 3x3 grid display
        self.grid_frame = tk.Frame(self, bg=self.cyan, bd=3, relief="ridge")
        self.grid_frame.pack(pady=10)
        
        self.buttons = []
        for i in range(9):
            btn = tk.Button(self.grid_frame, text="", width=4, height=2, font=("Courier New", 32, "bold"), 
                            bg=self.hot_pink, fg=self.yellow, disabledforeground=self.yellow, state=tk.DISABLED, relief="raised", bd=5)
            row, col = divmod(i, 3)
            btn.grid(row=row, column=col, padx=3, pady=3)
            self.buttons.append(btn)

        # load the target board on launch
        self.update_board(GOAL_STATE)

    def show_manual_input(self):
        # hide the initial buttons to keep the UI clean
        self.choice_frame.pack_forget()
        # pop the input box onto the screen right below the initial state label
        self.input_frame.pack(after=self.pack_slaves()[0], pady=5)
        self.input_entry.pack(pady=5)
        self.input_entry.focus_set()
        self.status_label.config(text="READY. ENTER BOARD AND SELECT SOLVER.")

    def load_from_file(self):
        # pop open the file browser
        filepath = filedialog.askopenfilename(filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")])
        if not filepath:
            return
            
        try:
            initial_state = []
            with open(filepath, 'r') as file:
                for line in file:
                    line = line.strip()
                    # ignore empty lines or the headers from the lab instructions
                    if not line or line.lower() in ["initial state", "goal state"]:
                        continue
                        
                    # parse the comma string just like in the notebook
                    row = ['' if x.strip() == '0' else int(x.strip()) for x in line.split(',')]
                    initial_state.extend(row)
                    
                    # stop reading once we have the first 9 tiles (ignoring the goal state part of the file)
                    if len(initial_state) >= 9:
                        break
                        
            if len(initial_state) == 9:
                # hide the buttons and reveal the text box containing the loaded data
                self.choice_frame.pack_forget()
                self.input_frame.pack(after=self.pack_slaves()[0], pady=5)
                self.input_entry.pack(pady=5)
                
                self.input_entry.delete(0, tk.END)
                self.input_entry.insert(0, str(initial_state))
                
                # refresh the visual grid
                self.update_board(self.parse_input())
                filename = filepath.split('/')[-1]
                self.status_label.config(text=f"LOADED FILE: {filename}")
            else:
                messagebox.showerror("ERROR", "Could not find a valid 3x3 comma-separated board in the file.")
                
        except Exception as e:
            messagebox.showerror("ERROR", f"Failed to read file: {e}")

    def parse_input(self):
        try:
            # safely evaluate the text box string
            state_in = ast.literal_eval(self.input_entry.get())
            if isinstance(state_in, list):
                # catch stray 0s or empty spaces and normalize them to ''
                state_in = ['' if (x == 0 or (isinstance(x, str) and x.strip() == '')) else x for x in state_in]
            if is_valid_state(state_in):
                return state_in
            messagebox.showerror("ERROR", "INVALID BOARD FORMAT.")
        except Exception:
            messagebox.showerror("ERROR", "SYNTAX ERROR IN INPUT.")
        return None

    def prep_solve(self):
        start_state = self.parse_input()
        if not start_state: return None
        
        self.update_board(start_state)
        
        # immediately block impossible puzzles to save compute
        if not is_solvable(start_state, GOAL_STATE):
            messagebox.showerror("PARITY ERROR", "This board configuration is mathematically unsolvable (Odd inversion parity vs Even goal).")
            self.status_label.config(text="ERROR: UNSOLVABLE BOARD.")
            return None
            
        self.status_label.config(text="SEARCHING... PLEASE WAIT.")
        self.update()
        return start_state

    def load_solution(self, path, moves, expanded, algo_name):
        self.solution_path = path
        self.solution_moves = moves
        self.current_step = 0
        
        cost = len(path) - 1
        self.status_label.config(text=f"{algo_name} SUCCESS | COST: {cost} | EXPANDED: {expanded}")
        self.update_nav_ui()
        self.update_board(self.solution_path[self.current_step])

    def solve_bfs(self):
        start_state = self.prep_solve()
        if not start_state: return
        path, moves, expanded = bfs(start_state, GOAL_STATE)
        if path:
            self.load_solution(path, moves, expanded, "BFS")
            
    def solve_astar(self):
        start_state = self.prep_solve()
        if not start_state: return
        path, moves, expanded = a_star_8_puzzle(start_state, GOAL_STATE)
        if path:
            self.load_solution(path, moves, expanded, "A*")

    def step_prev(self):
        # walk backward in the saved path
        if self.current_step > 0:
            self.current_step -= 1
            self.update_board(self.solution_path[self.current_step])
            self.update_nav_ui()

    def step_next(self):
        # walk forward in the saved path
        if self.current_step < len(self.solution_path) - 1:
            self.current_step += 1
            self.update_board(self.solution_path[self.current_step])
            self.update_nav_ui()

    def update_nav_ui(self):
        total_steps = len(self.solution_path) - 1
        if total_steps < 0: total_steps = 0
        
        if self.current_step == 0:
            move_text = "START"
        else:
            move_text = f"MOVE: {self.solution_moves[self.current_step - 1]}"
            
        self.step_label.config(text=f"STEP {self.current_step} / {total_steps}\n[{move_text}]")
        
        # toggle button states based on position
        self.prev_btn.config(state=tk.NORMAL if self.current_step > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if self.current_step < total_steps else tk.DISABLED)

    def update_board(self, state):
        # refresh all 9 tiles
        for i, val in enumerate(state):
            self.buttons[i].config(text=str(val))
            
            # sink the blank tile so it looks like a hole
            if val == '':
                self.buttons[i].config(bg=self.blank_color, relief="sunken", bd=1)
            else:
                self.buttons[i].config(bg=self.hot_pink, relief="raised", bd=5)

if __name__ == "__main__":
    app = EightPuzzleSolverGUI()
    app.mainloop()