// This file is released under the MIT license.
// See LICENSE.md.

function load_sudoku() {
  if (!board_blocked) {
    sudoku_initialize_board();
    sudoku_input = document.getElementById("sudoku-input").value;
    sudoku_load_from_string(sudoku_input);
    sudoku_render_board();
  }
}
function clear_sudoku() {
  if (!board_blocked) {
    sudoku_initialize_board();
    sudoku_render_board();
  }
}
function load_example_sudoku() {
  if (!board_blocked) {
    sudoku_initialize_board();
    sudoku_as_string = document.getElementById("example-sudokus").value;
    sudoku_load_from_string(sudoku_as_string);
    sudoku_render_board();
  }
}

interface_wait_time_propagate = null;

function interface_wait_time_propagate_round() {
  speed_factor = document.getElementById("speed").value;
  return speed_factor*500;
}

function interface_wait_time_decide() {
  speed_factor = document.getElementById("speed").value;
  return speed_factor*1000;
}

function interface_wait_time_learn() {
  speed_factor = document.getElementById("speed").value;
  return speed_factor*1000;
}

function interface_wait_time_backjump() {
  speed_factor = document.getElementById("speed").value;
  return speed_factor*1000;
}

function interface_wait_time_conflict() {
  speed_factor = document.getElementById("speed").value;
  return speed_factor*500;
}

var cur_level = 0;
var assignment = [];
var last_learned = [];

function interface_start() {
  should_abort = false;
  document.getElementById("btn_solve").disabled = true;
  document.getElementById("btn_pause").disabled = false;
  document.getElementById("btn_resume").disabled = true;
  document.getElementById("btn_abort").disabled = false;

  sudoku_initialize_candidates();
  sudoku_render_board();

  clearOutput();
  updateOutput();

  cur_level = 0;
  cur_assignment = [];
  last_learned = [];
}

function interface_assign(lit) {
  if (lit > 0) {
    var tuple = decode_var(lit);
    var i = tuple[0];
    var j = tuple[1];
    var v = tuple[2];
    var c = get_cell_no_from_coord(i, j);
    board[c].val = v;
  } else {
    var tuple = decode_var(-1*lit);
    var i = tuple[0];
    var j = tuple[1];
    var v = tuple[2];
    var c = get_cell_no_from_coord(i, j);
    var index = board[c].candidates.indexOf(v);
    if (index > -1) {
      board[c].candidates.splice(index, 1);
    }
  }
  // sudoku_render_board();
}

function interface_unassign(lit) {
  if (lit > 0) {
    var tuple = decode_var(lit);
    var i = tuple[0];
    var j = tuple[1];
    // var v = tuple[2];
    var c = get_cell_no_from_coord(i, j);
    board[c].val = null;
  } else {
    var tuple = decode_var(-1*lit);
    var i = tuple[0];
    var j = tuple[1];
    var v = tuple[2];
    var c = get_cell_no_from_coord(i, j);
    board[c].candidates.push(v);
  }
  // sudoku_render_board();
}

function interface_propagate(lit) {
  cur_assignment.push({
    level: cur_level,
    lit: lit,
    type: "prop",
  });
  interface_assign(lit);
}

function interface_done_propagating() {
  sudoku_render_board();
}

function interface_conflict(clause) {
  console.log("CONFLICT: [" + clause + "]");
}

function pretty_repr_lit(lit) {
  var n = lit;
  if (lit < 0) {
    n = -1*lit;
  }
  var tuple = decode_var(n);
  var i = tuple[0];
  var j = tuple[1];
  var v = tuple[2];
  var pretty_repr = "solution(" + (i+1) + "," + (j+1) + "," + v + ")";
  if (lit > 0) {
    return pretty_repr;
  } else {
    return "-" + pretty_repr;
  }
}

function interface_learned_clause(clause) {
  addToOutput("[" + clause.map(pretty_repr_lit) + "]");
  last_learned = clause;
}

function interface_analyze(conflict_graph) {
}

function interface_backjump(level) {
  console.log("BACKJUMPING TO LEVEL: " + level);
  cur_level = level;
  for (let i = cur_assignment.length-1; i >= 0; i--) {
    if (cur_assignment[i].level > level) {
      interface_unassign(cur_assignment[i].lit);
    }
  }
  cur_assignment = cur_assignment.filter(obj =>
    obj.level <= level
  );
}

function interface_decide(lit) {
  console.log("DECIDING: " + lit);
  cur_level += 1;
  cur_assignment.push({
    level: cur_level,
    lit: lit,
    type: "decide",
  });
  interface_assign(lit);
}

function interface_result(result) {
  if (result == "SAT") {
    console.log("SATISFIABLE");
  } else if (result == "UNSAT") {
    console.log("UNSATISFIABLE");
  } else if (result == "ABORT") {
    console.log("ABORTED");
  }
}

function interface_finish() {
  document.getElementById("btn_solve").disabled = false;
  document.getElementById("btn_pause").disabled = true;
  document.getElementById("btn_resume").disabled = true;
  document.getElementById("btn_abort").disabled = true;
}

var can_continue = true;
var should_abort = false;

function do_pause() {
  can_continue = false;
  document.getElementById("btn_pause").disabled = true;
  document.getElementById("btn_resume").disabled = false;
}

function do_resume() {
  can_continue = true;
  document.getElementById("btn_pause").disabled = false;
  document.getElementById("btn_resume").disabled = true;
}

function do_abort() {
  should_abort = true;
  do_resume();
  document.getElementById("btn_pause").disabled = true;
  document.getElementById("btn_resume").disabled = true;
  document.getElementById("btn_abort").disabled = true;
}

function get_cell_no_from_coord(i, j) {
  return 9*parseInt(i) + parseInt(j);
}

function get_coord_from_cell_no(n) {
  n = parseInt(n);
  j = n % 9;
  i = (n-j)/9;
  return [i,j];
}

function encode_var(i, j, v) {
  return 81*parseInt(i) + 9*parseInt(j) + (parseInt(v)-1) + 1;
}

function decode_var(n) {
  n = parseInt(n);
  var v = (n-1) % 9;
  var j = ((n-1-v)/9) % 9;
  var i = ((n-1-v)/9-j) / 9;
  return [i,j,v+1];
}

var solve = async function () {

  interface_start();

  // Add facts to program
  var cnf_dimacs = "";
  for (cell_no in board) {
    if (board[cell_no].val != null) {
      cell_coord = get_coord_from_cell_no(cell_no);
      i = cell_coord[0];
      j = cell_coord[1];
      v = board[cell_no].val;
      cnf_dimacs += encode_var(i, j, v) + " 0\n";
    }
  }
  // Add constraints to program
  // - each cell has at least one value
  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      let clause = "";
      for (let v = 1; v <= 9; v++) {
        clause += encode_var(i, j, v) + " ";
      }
      cnf_dimacs += clause + "0\n";
    }
  }
  // - each cell has at most one value
  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      for (let v1 = 1; v1 <= 9; v1++) {
        for (let v2 = v1+1; v2 <= 9; v2++) {
          l1 = -1*encode_var(i, j, v1);
          l2 = -1*encode_var(i, j, v2);
          cnf_dimacs += l1 + " " + l2 + " 0\n";
        }
      }
    }
  }
  // - each value appears at most once in each row
  for (let i = 0; i < 9; i++) {
    for (let j1 = 0; j1 < 9; j1++) {
      for (let j2 = j1+1; j2 < 9; j2++) {
        for (let v = 1; v <= 9; v++) {
          l1 = -1*encode_var(i, j1, v);
          l2 = -1*encode_var(i, j2, v);
          cnf_dimacs += l1 + " " + l2 + " 0\n";
        }
      }
    }
  }
  // - each value appears at least once in each row
  for (let v = 1; v <= 9; v++) {
    for (let i = 0; i < 9; i++) {
      let clause = "";
      for (let j = 0; j < 9; j++) {
        clause += encode_var(i, j, v) + " ";
      }
      cnf_dimacs += clause + "0\n";
    }
  }
  // - each value appears at most once in each column
  for (let j = 0; j < 9; j++) {
    for (let i1 = 0; i1 < 9; i1++) {
      for (let i2 = i1+1; i2 < 9; i2++) {
        for (let v = 1; v <= 9; v++) {
          l1 = -1*encode_var(i1, j, v);
          l2 = -1*encode_var(i2, j, v);
          cnf_dimacs += l1 + " " + l2 + " 0\n";
        }
      }
    }
  }
  // - each value appears at least once in each column
  for (let v = 1; v <= 9; v++) {
    for (let j = 0; j < 9; j++) {
      let clause = "";
      for (let i = 0; i < 9; i++) {
        clause += encode_var(i, j, v) + " ";
      }
      cnf_dimacs += clause + "0\n";
    }
  }
  // - each value appears at most once in each block
  for (let bi = 0; bi < 3; bi++) {
    for (let bj = 0; bj < 3; bj++) {
      for (let li1 = 0; li1 < 3; li1++) {
        for (let lj1 = 0; lj1 < 3; lj1++) {
          for (let li2 = 0; li2 < 3; li2++) {
            for (let lj2 = 0; lj2 < 3; lj2++) {
              if (li1 != li2 || lj1 != lj2) {
                c1 = get_cell_no_from_coord(3*bi+li1, 3*bj+lj1);
                c2 = get_cell_no_from_coord(3*bi+li2, 3*bj+lj2);
                if (c1 < c2) {
                  for (let v = 1; v <= 9; v++) {
                    l1 = -1*encode_var(3*bi+li1, 3*bj+lj1, v);
                    l2 = -1*encode_var(3*bi+li2, 3*bj+lj2, v);
                    cnf_dimacs += l1 + " " + l2 + " 0\n";
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  // - each value appears at least once in each block
  for (let v = 1; v <= 9; v++) {
    for (let bi = 0; bi < 3; bi++) {
      for (let bj = 0; bj < 3; bj++) {
        let clause = "";
        for (let li = 0; li < 3; li++) {
          for (let lj = 0; lj < 3; lj++) {
            clause += encode_var(3*bi+li, 3*bj+lj, v) + " ";
          }
        }
        cnf_dimacs += clause + "0\n";
      }
    }
  }

  var solver = initSolver();

  var prop_budget = 100000;
  var conf_budget = 100000;
  var time_budget = 100000;

  var use_1uip = true;
  var use_2wl = true;

  var logger;
  logger = console.log;

  solver.parse(cnf_dimacs);
  var result = await solver.solve(logger, prop_budget, conf_budget, time_budget, use_2wl, use_1uip);

  if (result.status == SAT) {
    interface_result("SAT");
  } else if (result.status == UNSAT) {
    interface_result("UNSAT");
  } else {
    interface_result("ABORT");
  }

  interface_finish();
}

function clearOutput() {
  output = "";
}

function addToOutput(text) {
  output = text + "\n" + output;
  updateOutput();
}

function updateOutput() {
  if (outputElement) {
    var output_to_show = " ";
    if (output != "") {
      output_to_show = output;
    }
    outputElement.textContent = output_to_show;
    // outputElement.scrollTop = outputElement.scrollHeight; // focus on bottom
  }
}

var output = "Ready..";
var outputElement = document.getElementById('output');
updateOutput();

sudoku_initialize_board();
sudoku_render_board();
board_blocked = false;
