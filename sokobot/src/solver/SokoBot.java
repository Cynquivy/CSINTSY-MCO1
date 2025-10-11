// feel free to comment out the debug parts

package solver;

import java.util.*;

public class SokoBot {

  // direction vectors (row change, column change) for Up, Down, Left, Right
  private static final int[] DIR_ROW = {-1, 1, 0, 0};
  private static final int[] DIR_COL = {0, 0, -1, 1};
  private static final char[] MOVE_CHARS = {'u', 'd', 'l', 'r'};

  // Toggle deadlock pruning. Keep true for reasonable pruning; set false to disable.
  private static final boolean ENABLE_DEADLOCK = true;

  /**
   * solveSokobanPuzzle
   * Purpose: Solve the provided Sokoban level using BFS (minimize pushes).
   * Parameters:
   *  - width: number of columns in the grid
   *  - height: number of rows in the grid
   *  - mapData: 2D char array for static cells (walls '#', floor ' ', goals '.')
   *  - itemsData: 2D char array for movable items (player '@' or '+', boxes '$' or '*')
   * Return value: A string of move characters ("u,d,l,r") representing the full
   * sequence of player steps (walks between pushes + push moves). Returns empty
   * string when no solution is found.
   */
  public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {
    int rows = height;
    int cols = width;

    // find player, boxes and goals
    int playerStartPos = -1; // linearized index (row*cols + col)
    List<Integer> boxesStartList = new ArrayList<>();
    List<Integer> goalsList = new ArrayList<>();

    // itemsData has player/boxes, mapData has goals
    for (int r = 0; r < rows; r++) {
      for (int c = 0; c < cols; c++) {
        char mapChar = mapData[r][c];
        char itemChar = itemsData[r][c];
        // player: '@' = player on floor, '+' = player on goal
        if (itemChar == '@' || itemChar == '+') playerStartPos = r * cols + c;
        // box: '$' = box on floor, '*' = box on goal
        if (itemChar == '$' || itemChar == '*') boxesStartList.add(r * cols + c);
        // goal cell in map
        if (mapChar == '.') goalsList.add(r * cols + c);
      }
    }

    // Fallback parse: some loaders put everything in mapData (combined grid)
    if (playerStartPos == -1 || boxesStartList.isEmpty()) {
      for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
          char ch = mapData[r][c];
          if ((ch == '@' || ch == '+') && playerStartPos == -1) playerStartPos = r * cols + c;
          if (ch == '$' || ch == '*') boxesStartList.add(r * cols + c);
          if (ch == '.') goalsList.add(r * cols + c);
        }
      }
    }

    // I honestly don't know what this does but gpt told me to put it
    final Set<Integer> goalSet = new HashSet<>(goalsList);

    // Precompute conservative static dead cells (corners only)
    // A static-dead cell is a tile that is definitely unsafe for a box (no dynamic consideration of other boxes)
    boolean[] staticCornerDead = new boolean[rows * cols];
    for (int r = 0; r < rows; r++) {
      for (int c = 0; c < cols; c++) {
        int pos = r * cols + c;
        if (mapData[r][c] == '#') continue;           // walls are ignored
        if (goalSet.contains(pos)) continue;         // goals are never dead
        // check whether two orthogonal neighbours are walls/borders -> corner
        boolean upIsWall = isWallOrOutside(r - 1, c, mapData, rows, cols);
        boolean downIsWall = isWallOrOutside(r + 1, c, mapData, rows, cols);
        boolean leftIsWall = isWallOrOutside(r, c - 1, mapData, rows, cols);
        boolean rightIsWall = isWallOrOutside(r, c + 1, mapData, rows, cols);
        if ((upIsWall && leftIsWall) || (upIsWall && rightIsWall) ||
                (downIsWall && leftIsWall) || (downIsWall && rightIsWall)) {
          staticCornerDead[pos] = true;
        }
      }
    }

    /* DEBUG */
    System.out.println("[SokoBotDebug] rows=" + rows + " cols=" + cols);
    System.out.println("[SokoBotDebug] playerStart=" + playerStartPos + (playerStartPos == -1 ? "" : " (r=" + (playerStartPos / cols) + ",c=" + (playerStartPos % cols) + ")"));
    System.out.println("[SokoBotDebug] boxesCount=" + boxesStartList.size() + " boxes=" + boxesStartList);
    System.out.println("[SokoBotDebug] goalsCount=" + goalsList.size() + " goals=" + goalsList);
    System.out.println("[SokoBotDebug] ENABLE_DEADLOCK=" + ENABLE_DEADLOCK);

    if (playerStartPos == -1 || boxesStartList.isEmpty()) {
      System.out.println("[SokoBotDebug] invalid start or no boxes; returning empty solution");
      return ""; // nothing to solve
    }

    // Convert boxes to array and sort for canonical state representation
    int boxCount = boxesStartList.size();
    int[] boxesStart = new int[boxCount];
    for (int i = 0; i < boxCount; i++) boxesStart[i] = boxesStartList.get(i);
    Arrays.sort(boxesStart);

    // Initial state: box positions and player position
    State initialState = new State(boxesStart, playerStartPos);

    // BFS frontier (states reached by pushes)
    Queue<State> frontier = new ArrayDeque<>();
    frontier.add(initialState);

    // For reconstructing the full move sequence and for visited checks
    Map<String, ParentInfo> cameFrom = new HashMap<>();
    Set<String> visited = new HashSet<>();
    visited.add(initialState.key());

    final int MAX_EXPANSIONS = 500_000; // modifiable, it's there to not crash my pc
    int expansions = 0;

    // BFS main loop
    while (!frontier.isEmpty()) {
      State state = frontier.poll();
      expansions++;
      if (expansions > MAX_EXPANSIONS) break;

      // Goal check: all boxes are on goals after ___ BFS expansions
      if (allBoxesOnGoals(state.boxPositions, goalSet)) {
        System.out.println("[SokoBotDebug] Found solution after expansions=" + expansions);
        return reconstructSolution(state.key(), cameFrom); // Solved answer
      }

      // quick lookup to check walls
      boolean[] boxOccupied = new boolean[rows * cols];
      for (int b : state.boxPositions) boxOccupied[b] = true;

      // BFS from player's position to find reachable tiles without pushing boxes
      boolean[] playerReachable = bfsReachable(state.playerPos, boxOccupied, mapData, rows, cols);

      // DEBUG: show how many squares the player can currently reach
      int reachableCount = 0;
      for (boolean rch : playerReachable) if (rch) reachableCount++;
      System.out.println("[SokoBotDebug] expansion=" + expansions + " player=(r=" + (state.playerPos / cols)
              + ",c=" + (state.playerPos % cols) + ") boxes=" + Arrays.toString(state.boxPositions)
              + " reachableSquares=" + reachableCount);

      // Generate successor states by considering all legal pushes
      for (int i = 0; i < state.boxPositions.length; i++) {
        int boxPos = state.boxPositions[i];
        int boxRow = boxPos / cols;
        int boxCol = boxPos % cols;

        for (int dir = 0; dir < 4; dir++) {
          // player must stand on the opposite side of the direction to push
          int playerRow = boxRow - DIR_ROW[dir];
          int playerCol = boxCol - DIR_COL[dir];
          int destRow = boxRow + DIR_ROW[dir];
          int destCol = boxCol + DIR_COL[dir];

          // check bounds
          if (!inBounds(playerRow, playerCol, rows, cols) || !inBounds(destRow, destCol, rows, cols)) continue;

          int playerPushPos = playerRow * cols + playerCol; // where player must stand
          int destPos = destRow * cols + destCol;          // where the box will be pushed to

          // destination must be floor/goal and not occupied by another box
          if (mapData[destRow][destCol] == '#') continue;    // destination is a wall
          if (boxOccupied[destPos]) continue;                 // another box blocks destination

          // player must be able to reach the pushing square without moving boxes
          if (!playerReachable[playerPushPos]) continue;

          // Reconstruct the actual walking moves from player's pos to pushing pos
          String walkMoves = reconstructWalk(state.playerPos, playerPushPos, boxOccupied, mapData, rows, cols);
          if (walkMoves == null) {
            // This shouldn't happen because we already checked reachability, but be defensive
            System.out.println("[SokoBotDebug] Warning: reconstructWalk failed despite reachability");
            continue;
          }

          System.out.println("[SokoBotDebug] consider push: box@(r=" + boxRow + ",c=" + boxCol + ") -> (r=" + destRow + ",c=" + destCol + ") via p@(r=" + playerRow + ",c=" + playerCol + ") walkLen=" + walkMoves.length() + " push=" + MOVE_CHARS[dir]);

          // Simulate the push to form successor state
          int[] newBoxPositions = Arrays.copyOf(state.boxPositions, state.boxPositions.length);
          newBoxPositions[i] = destPos;
          Arrays.sort(newBoxPositions); // canonical ordering for hashing

          // Deadlock pruning: disallow pushing box into a static corner (unless it's a goal)
          if (ENABLE_DEADLOCK && staticCornerDead[destPos]) {
            System.out.println("[SokoBotDebug] skip: static corner dead at (r=" + destRow + ",c=" + destCol + ")");
            continue;
          }

          State successor = new State(newBoxPositions, boxPos); // player ends up where the box was
          String succKey = successor.key();
          if (visited.contains(succKey)) {
            System.out.println("[SokoBotDebug] skip: already visited");
            continue;
          }

          // The action is: walkMoves (sequence) then a single push character
          String action = walkMoves + MOVE_CHARS[dir];
          System.out.println("[SokoBotDebug] accepting push: action=" + action);

          cameFrom.put(succKey, new ParentInfo(state.key(), action));
          visited.add(succKey);
          frontier.add(successor);
        }
      }
    }

    // No solution found
    System.out.println("[SokoBotDebug] frontier exhausted after expansions=" + expansions + ", no solution");
    return "";
  }

  // HELPER CLASS & FUNCTIONS

  /**
   * State (constructor)
   * Purpose: represent a Sokoban state (array of box positions + player position).
   */
  private static class State {
    int[] boxPositions; // sorted box positions
    int playerPos;      // player position

    State(int[] boxPositions, int playerPos) {
      this.boxPositions = boxPositions;
      this.playerPos = playerPos;
    }

    /**
     * key
     * Purpose: produce a unique string key for the state for hashing/visited checks
     * Parameters: none
     * Return: String like "b1,b2,b3,|player"
     */
    String key() {
      StringBuilder sb = new StringBuilder();
      for (int p : boxPositions) { sb.append(p).append(','); }
      sb.append('|').append(playerPos);
      return sb.toString();
    }
  }

  /**
   * ParentInfo (constructor)
   * Purpose: store parent state key and the action (walks+push) used to reach child
   */
  private static class ParentInfo {
    String parentKey;      // key of the parent state
    String actionFromParent; // sequence of player moves (walks + one push char)

    ParentInfo(String parentKey, String action) {
      this.parentKey = parentKey;
      this.actionFromParent = action;
    }
  }

  /**
   * allBoxesOnGoals
   * Purpose: check whether every box is currently on a goal tile
   * Parameters: boxes (int[]), goals (Set<Integer>)
   * Return: true if all boxes are on goals, false otherwise
   */
  private boolean allBoxesOnGoals(int[] boxes, Set<Integer> goals) {
    for (int b : boxes) if (!goals.contains(b)) return false;
    return true;
  }

  /**
   * inBounds
   * Purpose: check if a row/col is inside the grid
   * Parameters: row, col, totalRows, totalCols
   * Return: boolean
   */
  private boolean inBounds(int row, int col, int totalRows, int totalCols) {
    return row >= 0 && row < totalRows && col >= 0 && col < totalCols;
  }

  /**
   * isWallOrOutside
   * Purpose: return true if the cell is a wall or outside the map
   * Parameters: row, col, mapData, rows, cols
   * Return: boolean
   */
  private boolean isWallOrOutside(int row, int col, char[][] mapData, int rows, int cols) {
    if (!inBounds(row, col, rows, cols)) return true;
    return mapData[row][col] == '#';
  }

  /**
   * bfsReachable
   * Purpose: compute which tiles the player can reach without pushing boxes
   * Parameters:
   *  - startPos: linearized player start
   *  - boxOccupied: boolean[] marking occupied tiles by boxes
   *  - mapData, rows, cols: map geometry
   * Return: boolean[] of reachable tiles
   */
  private boolean[] bfsReachable(int startPos, boolean[] boxOccupied, char[][] mapData, int rows, int cols) {
    boolean[] reachable = new boolean[rows * cols];
    int N = rows * cols;
    if (startPos < 0 || startPos >= N) return reachable;
    Queue<Integer> q = new ArrayDeque<>();
    reachable[startPos] = true;
    q.add(startPos);
    while (!q.isEmpty()) {
      int pos = q.poll();
      int r = pos / cols;
      int c = pos % cols;
      for (int d = 0; d < 4; d++) {
        int nr = r + DIR_ROW[d];
        int nc = c + DIR_COL[d];
        if (!inBounds(nr, nc, rows, cols)) continue;
        if (mapData[nr][nc] == '#') continue; // wall
        int npos = nr * cols + nc;
        if (boxOccupied[npos]) continue;      // another box blocks
        if (!reachable[npos]) {
          reachable[npos] = true;
          q.add(npos);
        }
      }
    }
    return reachable;
  }

  /**
   * reconstructWalk
   * Purpose: find a sequence of player moves from startPos to goalPos avoiding boxes
   * Parameters: startPos, goalPos, boxOccupied, mapData, rows, cols
   * Return: String of moves ("udlr"), or null if unreachable
   */
  private String reconstructWalk(int startPos, int goalPos, boolean[] boxOccupied, char[][] mapData, int rows, int cols) {
    if (startPos == goalPos) return "";
    int N = rows * cols;
    if (startPos < 0 || startPos >= N || goalPos < 0 || goalPos >= N) return null;

    boolean[] visited = new boolean[N];
    int[] prev = new int[N];
    Arrays.fill(prev, -1);
    int[] prevMove = new int[N];
    Queue<Integer> q = new ArrayDeque<>();
    visited[startPos] = true;
    q.add(startPos);
    boolean found = false;

    while (!q.isEmpty()) {
      int pos = q.poll();
      int r = pos / cols;
      int c = pos % cols;
      for (int d = 0; d < 4; d++) {
        int nr = r + DIR_ROW[d];
        int nc = c + DIR_COL[d];
        if (!inBounds(nr, nc, rows, cols)) continue;
        if (mapData[nr][nc] == '#') continue;
        int npos = nr * cols + nc;
        if (boxOccupied[npos]) continue;
        if (visited[npos]) continue;
        visited[npos] = true;
        prev[npos] = pos;
        prevMove[npos] = d;
        if (npos == goalPos) { found = true; break; }
        q.add(npos);
      }
      if (found) break;
    }

    if (!found) return null;
    StringBuilder sb = new StringBuilder();
    int cur = goalPos;
    while (cur != startPos) {
      int d = prevMove[cur];
      sb.append(MOVE_CHARS[d]);
      cur = prev[cur];
    }
    return sb.reverse().toString();
  }

  /**
   * reconstructSolution
   * Purpose: reconstruct full move sequence from the start to a goal state
   * Parameters: goalKey (String key for the final state), cameFrom map
   * Return: concatenated action string (walks + pushes) from start -> goal
   */
  private String reconstructSolution(String goalKey, Map<String, ParentInfo> cameFrom) {
    List<String> actions = new ArrayList<>();
    String curKey = goalKey;
    while (cameFrom.containsKey(curKey)) {
      ParentInfo p = cameFrom.get(curKey);
      actions.add(p.actionFromParent);
      curKey = p.parentKey;
    }
    Collections.reverse(actions);
    StringBuilder sb = new StringBuilder();
    for (String a : actions) sb.append(a);
    return sb.toString();
  }
}
