# Gitting good in e^pi steps

# The setup

1. Create your personal account for GitHub
[https://github.com/join]([https://github.com/join)

2. Fork edgarcosta/hilbertmodularforms
 * go to https://github.com/edgarcosta/hilbertmodularforms/
 * click the fork button

3. If you don't have a pair of public/private RSA keys, create one, by doing:
`ssh-keygen`.
Now copy the content of your public key `~/.ssh/id_rsa.pub`, you can access the content of the file by doing `cat ~/.ssh/id_rsa.pub`,
and add it to [https://github.com/settings/keys](https://github.com/settings/keys).

4. Open a terminal on your computer, and go to a folder where you would like to store your personal copy of `hilbertmodularforms`
 For example: `cd secretprojets/`

5. Clone your repository to your computer by doing:
  ```
  git clone git@github.com:YOURUSERNAME/hilbertmodularforms.git NAMEDESIRED
  ```
  where you replace `YOURUSERNAME` and `NAMEDESIRED`.
  `NAMEDESIRED` is the name of the folder where it will store your personal copy of `hilbertmodularforms`

6. Change directory to the directory you just created, e.g, `cd NAMEDESIRED`

7. You also want to be able to access the changes of other people on the main repository, for that we need to manually add it, by doing:
  ```
  git remote add upstream git@github.com:edgarcosta/hilbertmodularforms.git
  ```


# The development routine

## Creating a branch which is up to date with the main repository
1. Download the latest changes of the main repository to your computer with
  `git fetch upstream master`
  2. Change the code on your directory to reflect the latest changes with `git checkout upstream/master`
  3. Now that you are up to date, you should create a branch which will track the new changes, with ` git checkout -b NEWBRANCHNAME`

## Saving changes
  1. Do `git status` to see what files you have edited
  2. Do `git add FILENAME` for each file you would like submit changes
  3. Commit your changes on your computer with
  ```
  git commit
  ```
  alternatively, if you want to skip the editor, you can also do:
  ```
  git commit -m "fixed something really important"
  ```
  4. Push your changes to the internet
  ```
  git push
  ```
  if you have never pushed this branch, then it will complain and tell you what to do

## Merging my changes with the main repository
  1. Create a PR
  2. Merge the PR, you can also ask someone to quickly look into it

## Switching between branches
  You can switch between branches by doing:
  `git checkout BRANCHNAME`

## Merging the changes from the main repository
Imagine that someone has been working hard, and just merged some code that you need to the main repository.
You can merge this changes, with your current branch by doing
  ```
  git pull upstream master
  ```

# Remarks

# Exercises

1. Edit the `README.md` and `LICENSE` file and add your name
