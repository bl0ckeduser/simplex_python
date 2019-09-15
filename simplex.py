import copy
import fractions

# simplex_python
#
# by Gabriel, 2019
#
# Public Domain
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
# OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
# ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.
#

class SimplexVectorEntry:
    def __init__(self, variable_index, coefficient):
        self.variable_index = variable_index
        self.coefficient = fractions.Fraction(coefficient)

    def __str__(self):
        return '{0}x_{1}'.format(str(self.coefficient), str(self.variable_index))

    def copy(self):
        the_clone = SimplexVectorEntry(self.variable_index, self.coefficient)

    __copy__ = copy

class SimplexVector:
    def __init__(self):
        self.index = -1
        self.name = ''
        self.constant_term = fractions.Fraction(0)
        self.entries = []
    
    def copy(self):
        the_clone = SimplexVector()
        the_clone.index = self.index
        the_clone.name = self.name
        the_clone.constant_term = self.constant_term
        the_clone.entries = copy.deepcopy(self.entries)

    __copy__ = copy

    def __str__(self):
        ret = ''
        if self.index > 0:
            ret += 'x_' + str(self.index) + ' = '
        if self.constant_term != fractions.Fraction(0):
            ret += str(self.constant_term) + ' + '
        for i in range(len(self.entries)):
            if i > 0:
                ret += ' + '
            ret += str(self.entries[i])
        return ret

class SimplexDictionary:
    def __init__(self):
        self.z = None
        self.basis = None
        self.initial_basic_variables_max_index = 0
    
    def __str__(self):
        retbuf = 'z = ' + str(self.z) + '\n----------------------\n'
        for be in self.basis:
            retbuf += str(be) + '\n'
        return retbuf

    def copy(self):
        the_clone = SimplexDictionary()
        the_clone.basis = copy.deepcopy(self.basis)
        the_clone.initial_basic_variables_max_index = self.initial_basic_variables_max_index
        the_clone.z = copy.deepcopy(z)
        return the_clone

    __copy__ = copy

class Simplex:
    def __init__(self):
        pass

    def iterate(self, d, verbose=False): 
        # Find the highest-indexed variable in the objective function
        # 'z' with nonnegative coefficient (for some very sneaky and subtle 
        # reason this works better than taking the lowest always which 
        # is known as Bland's rule)
        index = -1
        match_key = 0
        for i in range(len(d.z.entries)):
            if d.z.entries[i].coefficient > fractions.Fraction(0):
                if index == -1 or d.z.entries[i].variable_index > match_key:
                    match_key = d.z.entries[i].variable_index
                    index = i

        if index == -1:
            print('Finding index: operation failed; halting')
            return False

        if verbose is True:
            print('Selected first variable for pivot = x_{0}'.format(str(match_key)))
            print('Constraint bounds...')

        # Find the basic variable which imposes the tightest
        # <= constraint on the selected variable
        index2 = -1
        constr_val = fractions.Fraction(0)
        for i in range(len(d.basis)):
            for j in range(len(d.basis[i].entries)):
                if d.basis[i].entries[j].variable_index == match_key and d.basis[i].entries[j].coefficient != fractions.Fraction(0):
                    this_constr_val = fractions.Fraction()
                    if d.basis[i].entries[j].coefficient < fractions.Fraction(0):
                        # <=
                        this_constr_val = d.basis[i].constant_term / (-d.basis[i].entries[j].coefficient)
                        if verbose is True:
                            print('x_{0} : <= {1}'.format(str(d.basis[i].index), str(this_constr_val)))
                        if index2 == -1 or this_constr_val < fractions.Fraction(0):
                            index2 = i
                            constr_val = this_constr_val
                    else:
                        # >=
                        this_constr_val = d.basis[i].constant_term / (-d.basis[i].entries[j].coefficient)
                        if verbose is True:
                            print('x_{0} : >= {1}'.format(str(d.basis[i].index), str(this_constr_val)))

        if index2 == -1:
            print('Finding index2: operation failed; halting')
            return False
        
        if verbose is True:
            print('Selected second variable for pivot: x_{0}'.format(str(d.basis[index2].index)))
            print('Pivot: {0}, {1}'.format(str(match_key), str(d.basis[index2].index)))

        # Now we pivot index, index2
        second_variable_for_pivot = copy.deepcopy(d.basis[index2])
        coeff = fractions.Fraction(0)
        for i in second_variable_for_pivot.entries:
            if i.variable_index == match_key:
                coeff = i.coefficient
                second_variable_for_pivot.entries.remove(i)
                break

        if coeff == fractions.Fraction(0):
            print('Operation failed; halting')
            return False

        second_variable_for_pivot.constant_term = second_variable_for_pivot.constant_term / (coeff * fractions.Fraction(-1))
        second_variable_for_pivot.index = match_key

        for i in second_variable_for_pivot.entries:
            i.coefficient = i.coefficient / (coeff * fractions.Fraction(-1))

        negative_of_second_variable_for_pivot = SimplexVectorEntry(d.basis[index2].index, fractions.Fraction(1) / coeff)
        second_variable_for_pivot.entries.append(negative_of_second_variable_for_pivot)

        z_new = self.pivot_do_substitute(match_key, second_variable_for_pivot, d.z, True)

        if z_new is None:
            print('Operation failed; halting')
            return False

        index_to_remove = -1
        for i in range(len(d.basis)):
            if d.basis[i].index != match_key and d.basis[i].index != d.basis[index2].index:
                basis_entry_new = self.pivot_do_substitute(match_key, second_variable_for_pivot, d.basis[i], False)
                d.basis[i] = basis_entry_new

            if d.basis[i].index == d.basis[index2].index:
                index_to_remove = i

        if index_to_remove != -1:
            d.basis.remove(d.basis[index_to_remove])

        d.basis.append(second_variable_for_pivot)
        d.z = z_new
        return True

    def pivot_do_substitute(self, match_key, second_variable_for_pivot, source_for_substitution, must_find_variable_in_orig):
        orig = copy.deepcopy(source_for_substitution)
        index_of_first_variable_for_pivot = -1
        coeff_of_first_variable_for_pivot_in_source = fractions.Fraction(0)
        for i in range(len(orig.entries)):
            if orig.entries[i].variable_index == match_key:
                index_of_first_variable_for_pivot = i
                coeff_of_first_variable_for_pivot_in_source = orig.entries[i].coefficient
                break

        if index_of_first_variable_for_pivot == -1:
            if must_find_variable_in_orig:
                return None
            else:
                return source_for_substitution
        
        new_vector = copy.deepcopy(source_for_substitution)
        new_vector.entries.remove(new_vector.entries[index_of_first_variable_for_pivot])
        new_vector.constant_term += coeff_of_first_variable_for_pivot_in_source * second_variable_for_pivot.constant_term
        
        for i in range(len(second_variable_for_pivot.entries)):
            variable_match_index = -1
            for j in range(len(new_vector.entries)):
                if new_vector.entries[j].variable_index == second_variable_for_pivot.entries[i].variable_index:
                    variable_match_index = j
                    break
            new_coeff = coeff_of_first_variable_for_pivot_in_source * second_variable_for_pivot.entries[i].coefficient
            if variable_match_index != -1:
                new_vector.entries[variable_match_index].coefficient += new_coeff
            else:
                new_entry = SimplexVectorEntry(second_variable_for_pivot.entries[i].variable_index, new_coeff)
                new_vector.entries.append(new_entry)

        return copy.deepcopy(new_vector)

    def check_is_done(self, d):
        done = True
        for i in range(len(d.z.entries)):
            if d.z.entries[i].coefficient > fractions.Fraction(0):
                done = False
                break
        return done

    def do_simplex(self, d, verbose=False, show_dicts=False):
        while True:
            if verbose is True or show_dicts is True:
                print(str(d))
            if self.iterate(d, verbose) is False:
                print('Error reported; halting')
                return False
            if verbose is True or show_dicts is True:
                print(str(d))
            if self.check_is_done(d) is True:
                break

        # Infeasible result ?
        for i in range(len(d.basis)):
            if d.basis[i].constant_term < fractions.Fraction(0):
                return False

        return True

if __name__ == '__main__':
    initial = SimplexDictionary()
    initial.z = SimplexVector()
    initial.z.index = 0
    initial.z.name = 'z'
    initial.z.entries = []
    initial.z.entries.append(SimplexVectorEntry(1, 3))
    initial.z.entries.append(SimplexVectorEntry(2, 2))
    initial.basis = []
    x3 = SimplexVector()
    x3.index = 3
    x3.constant_term = fractions.Fraction(5)
    x3.entries = []
    x3.entries.append(SimplexVectorEntry(1, -1))
    x3.entries.append(SimplexVectorEntry(2, -1))
    initial.basis.append(x3)
    x4 = SimplexVector()
    x4.index = 4
    x4.constant_term = fractions.Fraction(6)
    x4.entries = []
    x4.entries.append(SimplexVectorEntry(1, -2))
    x4.entries.append(SimplexVectorEntry(2, -1))
    initial.basis.append(x4)
    x5 = SimplexVector()
    x5.index = 5
    x5.constant_term = fractions.Fraction(2)
    x5.entries = []
    x5.entries.append(SimplexVectorEntry(1, -1))
    initial.basis.append(x5)

    s = Simplex()
    s.do_simplex(initial, True, True)
    print('=====================================')

    initial = SimplexDictionary()
    initial.z = SimplexVector()
    initial.z.index = 0
    initial.z.name = 'z'
    initial.z.entries = []
    initial.z.entries.append(SimplexVectorEntry(1, 2))
    initial.z.entries.append(SimplexVectorEntry(2, -1))
    initial.basis = []
    x3 = SimplexVector()
    x3.index = 3
    x3.constant_term = fractions.Fraction(0)
    x3.entries = []
    x3.entries.append(SimplexVectorEntry(1, -1))
    x3.entries.append(SimplexVectorEntry(2, 1))
    initial.basis.append(x3)
    x4 = SimplexVector()
    x4.index = 4
    x4.constant_term = fractions.Fraction(10)
    x4.entries = []
    x4.entries.append(SimplexVectorEntry(2, -1))
    initial.basis.append(x4)

    s.do_simplex(initial, True, True)
    
