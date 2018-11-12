
// Start Linked List Implementation
typedef struct list* list;
struct list {
    void *data; // generic data
    list next;
};

void list_free(list p, void (*data_free)(void *x)) {
    while (p != NULL) {
        list q = p->next;
        if (p->data != NULL && data_free != NULL) {
            (*data_free)(p->data);
        }
        free(p);
        p = q;
    }
    return;
}

bool is_segment(list start, list end) {
    list p = start;
    while (p != end) {
        if (p == NULL) {
            return false;
        }
        p = p->next;
    }
    return true;
}

bool is_circular(list l) {
    if (l == NULL) {
        return false;
    }
    list t = l; // tortoise
    list h = l->next; // hare
    ASSERT(is_segment(t, h));
    while (t != h) {
        ASSERT(is_segment(t, h));
        if (h == NULL || h->next == NULL) {
            return false;
        }
        t = t->next;
        h = h->next->next;
    }
    return true;
}
// End Linked List Implementation

// Start Stack Implementation
typedef struct stack* stack;
struct stack {
    list top;
};

bool is_stack(stack S) {
    return is_segment(S->top, NULL);
}

bool stack_empty(stack S) {
    ASSERT(is_stack(S));
    return S->top == NULL;
}

stack stack_new() {
    ASSERT(true);
    stack S = xmalloc(sizeof(struct stack));
    S->top = NULL;
    ASSERT(is_stack(S) && stack_empty(S));
    return S;
}

void stack_free(stack S, void (*data_free)(void* x)) {
    ASSERT(is_stack(S));
    list_free(S->top, data_free);
    free(S);
}

void push(void* x, stack S) {
    ASSERT(is_stack(S));
    list first = xmalloc(sizeof(struct list));
    first->data = x;
    first->next = S->top;
    S->top = first;
    ASSERT(is_stack(S) && !stack_empty(S));
}

void* pop(stack S) {
    ASSERT(is_stack(S) && !stack_empty(S));
    ASSERT(S != NULL && S->top != NULL);
    void* x = S->top->data;
    list q = S->top;
    S->top = S->top->next;
    free(q);
    ASSERT(is_stack(S));
    return x;
}
// End Stack Implementation

