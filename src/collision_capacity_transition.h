#ifndef NFIELD_COLLISION_CAPACITY_TRANSITION_H
#define NFIELD_COLLISION_CAPACITY_TRANSITION_H

/* Finite numerical evaluations. No asymptotic or infinite-limit certification. */
typedef struct {
    int limit;
    int *mu;
    unsigned char *prime;
    long double *a, *mass, *sum_a, *deficit, *diagonal;
} CollisionTransition;

int collision_transition_init(CollisionTransition *t, int limit);
void collision_transition_clear(CollisionTransition *t);
long double collision_transition_cutoff(const CollisionTransition *t, int n, int m);
long double collision_transition_centered(const CollisionTransition *t, int n);
long double collision_transition_residual(const CollisionTransition *t, int n);
int collision_capacity_transition_command(int argc, char **argv);
int collision_capacity_transition_verify(void);
void collision_capacity_transition_help(void);

#endif
