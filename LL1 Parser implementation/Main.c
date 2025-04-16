#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#define MAX_PROD 10
#define MAX_SYMBOLS 10

char productions[MAX_PROD][MAX_SYMBOLS];
int num_productions;

typedef struct {
    char symbol;
    char first_set[MAX_SYMBOLS];
    int first_count;
    char follow_set[MAX_SYMBOLS];
    int follow_count;
} NonTerminal;

NonTerminal non_terminals[MAX_SYMBOLS];
int num_non_terminals = 0;

char terminals[MAX_SYMBOLS];
int num_terminals = 0;

char parsing_table[MAX_SYMBOLS][MAX_SYMBOLS][MAX_SYMBOLS]; // table[non_term][term][prod]

int get_non_terminal_index(char c) {
    for (int i = 0; i < num_non_terminals; i++) {
        if (non_terminals[i].symbol == c)
            return i;
    }
    return -1;
}

int get_terminal_index(char c) {
    for (int i = 0; i < num_terminals; i++) {
        if (terminals[i] == c)
            return i;
    }
    return -1;
}

void add_to_first(int nt_index, char symbol) {
    for (int i = 0; i < non_terminals[nt_index].first_count; i++) {
        if (non_terminals[nt_index].first_set[i] == symbol)
            return;
    }
    non_terminals[nt_index].first_set[non_terminals[nt_index].first_count++] = symbol;
}

void add_to_follow(int nt_index, char symbol) {
    for (int i = 0; i < non_terminals[nt_index].follow_count; i++) {
        if (non_terminals[nt_index].follow_set[i] == symbol)
            return;
    }
    non_terminals[nt_index].follow_set[non_terminals[nt_index].follow_count++] = symbol;
}

void compute_first(char symbol) {
    int nt_index = get_non_terminal_index(symbol);
    if (nt_index != -1) {
        // Non-terminal already processed
        if (non_terminals[nt_index].first_count > 0)
            return;
    } else {
        // Terminal
        return;
    }

    for (int i = 0; i < num_productions; i++) {
        if (productions[i][0] != symbol) continue;

        char *prod = productions[i] + 2;
        if (prod[0] == '#') { // Epsilon
            add_to_first(nt_index, '#');
            continue;
        }

        for (int j = 0; prod[j] != '\0'; j++) {
            char current = prod[j];
            if (isupper(current)) { // Non-terminal
                int current_nt = get_non_terminal_index(current);
                if (current_nt == -1) {
                    // Add new non-terminal
                    non_terminals[num_non_terminals].symbol = current;
                    current_nt = num_non_terminals++;
                }
                compute_first(current);
                // Copy first set excluding epsilon
                for (int k = 0; k < non_terminals[current_nt].first_count; k++) {
                    if (non_terminals[current_nt].first_set[k] != '#') {
                        add_to_first(nt_index, non_terminals[current_nt].first_set[k]);
                    }
                }
                // If epsilon not in first, stop
                int has_epsilon = 0;
                for (int k = 0; k < non_terminals[current_nt].first_count; k++) {
                    if (non_terminals[current_nt].first_set[k] == '#') {
                        has_epsilon = 1;
                        break;
                    }
                }
                if (!has_epsilon) break;
                // If last symbol and has epsilon, add epsilon to first
                if (prod[j + 1] == '\0') {
                    add_to_first(nt_index, '#');
                }
            } else { // Terminal
                add_to_first(nt_index, current);
                break;
            }
        }
    }
}

void compute_follow(char symbol) {
    int nt_index = get_non_terminal_index(symbol);
    if (nt_index == -1) return;

    // Rule 1: Start symbol has $ in follow
    if (symbol == productions[0][0]) {
        add_to_follow(nt_index, '$');
    }

    for (int i = 0; i < num_productions; i++) {
        char *prod = productions[i] + 2;
        for (int j = 0; prod[j] != '\0'; j++) {
            if (prod[j] == symbol) {
                // Next character
                if (prod[j + 1] != '\0') {
                    char next = prod[j + 1];
                    if (isupper(next)) { // Non-terminal
                        int next_nt = get_non_terminal_index(next);
                        // Add first of next to follow of current
                        for (int k = 0; k < non_terminals[next_nt].first_count; k++) {
                            if (non_terminals[next_nt].first_set[k] != '#') {
                                add_to_follow(nt_index, non_terminals[next_nt].first_set[k]);
                            }
                        }
                        // If next has epsilon, add follow of left side
                        int has_epsilon = 0;
                        for (int k = 0; k < non_terminals[next_nt].first_count; k++) {
                            if (non_terminals[next_nt].first_set[k] == '#') {
                                has_epsilon = 1;
                                break;
                            }
                        }
                        if (has_epsilon) {
                            int lhs_nt = get_non_terminal_index(productions[i][0]);
                            for (int k = 0; k < non_terminals[lhs_nt].follow_count; k++) {
                                add_to_follow(nt_index, non_terminals[lhs_nt].follow_set[k]);
                            }
                        }
                    } else { // Terminal
                        add_to_follow(nt_index, next);
                    }
                } else { // End of production, add follow of lhs
                    int lhs_nt = get_non_terminal_index(productions[i][0]);
                    for (int k = 0; k < non_terminals[lhs_nt].follow_count; k++) {
                        add_to_follow(nt_index, non_terminals[lhs_nt].follow_set[k]);
                    }
                }
            }
        }
    }
}

void build_parsing_table() {
    for (int i = 0; i < num_productions; i++) {
        char lhs = productions[i][0];
        char *rhs = productions[i] + 2;
        int lhs_nt = get_non_terminal_index(lhs);

        // Compute first of rhs
        char first_rhs[MAX_SYMBOLS] = {0};
        int first_rhs_count = 0;
        int has_epsilon = 0;

        for (int j = 0; rhs[j] != '\0'; j++) {
            char current = rhs[j];
            if (isupper(current)) { // Non-terminal
                int current_nt = get_non_terminal_index(current);
                for (int k = 0; k < non_terminals[current_nt].first_count; k++) {
                    if (non_terminals[current_nt].first_set[k] != '#') {
                        first_rhs[first_rhs_count++] = non_terminals[current_nt].first_set[k];
                    }
                }
                // Check if current non-terminal has epsilon
                int epsilon_found = 0;
                for (int k = 0; k < non_terminals[current_nt].first_count; k++) {
                    if (non_terminals[current_nt].first_set[k] == '#') {
                        epsilon_found = 1;
                        break;
                    }
                }
                if (!epsilon_found) break;
                if (rhs[j + 1] == '\0') {
                    has_epsilon = 1;
                }
            } else { // Terminal
                if (current == '#') {
                    has_epsilon = 1;
                } else {
                    first_rhs[first_rhs_count++] = current;
                }
                break;
            }
        }

        if (has_epsilon) {
            for (int j = 0; j < non_terminals[lhs_nt].follow_count; j++) {
                char term = non_terminals[lhs_nt].follow_set[j];
                int term_idx = get_terminal_index(term);
                if (term_idx == -1) continue;
                strcpy(parsing_table[lhs_nt][term_idx], productions[i]);
            }
        } else {
            for (int j = 0; j < first_rhs_count; j++) {
                char term = first_rhs[j];
                int term_idx = get_terminal_index(term);
                if (term_idx == -1) continue;
                strcpy(parsing_table[lhs_nt][term_idx], productions[i]);
            }
        }
    }
}

void print_parsing_table() {
    printf("\nParsing Table:\n");
    printf("%-10s", "");
    for (int i = 0; i < num_terminals; i++) {
        printf("%-10c", terminals[i]);
    }
    printf("\n");
    for (int i = 0; i < num_non_terminals; i++) {
        printf("%-10c", non_terminals[i].symbol);
        for (int j = 0; j < num_terminals; j++) {
            if (parsing_table[i][j][0] != '\0') {
                printf("%-10s", parsing_table[i][j]);
            } else {
                printf("%-10s", "");
            }
        }
        printf("\n");
    }
}

int parse_input(char *input) {
    char stack[100];
    int top = 0;
    stack[top++] = '$';
    stack[top] = productions[0][0]; // Start symbol

    int input_ptr = 0;
    input[strlen(input)] = '$'; // Append end marker

    printf("\n%-20s%-20s%-20s\n", "Stack", "Input", "Action");
    while (top > 0) {
        // Print stack
        char stack_str[100] = "";
        for (int i = 0; i <= top; i++) {
            char c[2] = {stack[i], '\0'};
            strcat(stack_str, c);
        }
        // Print input
        char input_str[100] = "";
        strcpy(input_str, input + input_ptr);
        // Print action
        printf("%-20s%-20s", stack_str, input_str);

        char current = stack[top];
        char lookahead = input[input_ptr];

        if (current == lookahead) {
            printf("Match '%c'\n", current);
            top--;
            input_ptr++;
            continue;
        }

        int nt_index = get_non_terminal_index(current);
        if (nt_index == -1) {
            printf("\nError: Unexpected symbol '%c'\n", current);
            return 0;
        }

        int term_index = get_terminal_index(lookahead);
        if (term_index == -1) {
            printf("\nError: Invalid terminal '%c'\n", lookahead);
            return 0;
        }

        char *production = parsing_table[nt_index][term_index];
        if (production[0] == '\0') {
            printf("\nError: No production for %c on '%c'\n", current, lookahead);
            return 0;
        }

        printf("Apply %s\n", production);

        // Pop current non-terminal
        top--;
        // Push production rhs (skip lhs and '=')
        char *rhs = production + 2;
        if (rhs[0] != '#') { // Skip epsilon
            for (int i = strlen(rhs) - 1; i >= 0; i--) {
                stack[++top] = rhs[i];
            }
        }
    }

    return 1;
}

int main() {
    printf("Enter number of productions: ");
    scanf("%d", &num_productions);
    printf("Enter productions (format A=XYZ, use # for epsilon):\n");
    for (int i = 0; i < num_productions; i++) {
        scanf("%s", productions[i]);
        // Add non-terminal if not exists
        char lhs = productions[i][0];
        if (get_non_terminal_index(lhs) == -1) {
            non_terminals[num_non_terminals++].symbol = lhs;
        }
        // Collect terminals
        char *rhs = productions[i] + 2;
        for (int j = 0; rhs[j] != '\0'; j++) {
            if (!isupper(rhs[j]) && rhs[j] != '#') {
                int found = 0;
                for (int k = 0; k < num_terminals; k++) {
                    if (terminals[k] == rhs[j]) {
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    terminals[num_terminals++] = rhs[j];
                }
            }
        }
    }
    terminals[num_terminals++] = '$'; // Add end marker

    // Compute first sets
    for (int i = 0; i < num_non_terminals; i++) {
        compute_first(non_terminals[i].symbol);
    }

    // Compute follow sets
    for (int i = 0; i < num_non_terminals; i++) {
        compute_follow(non_terminals[i].symbol);
    }

    // Print first and follow sets
    printf("\nFirst sets:\n");
    for (int i = 0; i < num_non_terminals; i++) {
        printf("%c: { ", non_terminals[i].symbol);
        for (int j = 0; j < non_terminals[i].first_count; j++) {
            printf("%c ", non_terminals[i].first_set[j]);
        }
        printf("}\n");
    }

    printf("\nFollow sets:\n");
    for (int i = 0; i < num_non_terminals; i++) {
        printf("%c: { ", non_terminals[i].symbol);
        for (int j = 0; j < non_terminals[i].follow_count; j++) {
            printf("%c ", non_terminals[i].follow_set[j]);
        }
        printf("}\n");
    }

    build_parsing_table();
    print_parsing_table();

    char input[100];
    printf("\nEnter input string: ");
    scanf("%s", input);
    if (parse_input(input)) {
        printf("\nInput is valid\n");
    } else {
        printf("\nInput is invalid\n");
    }

    return 0;
}
